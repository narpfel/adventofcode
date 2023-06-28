#!/usr/bin/env python3

import re
from bisect import bisect_left
from functools import partial
from operator import attrgetter

from attr import attrib
from attr import attrs

GROUP_RE = re.compile(
    r"(?P<unit_count>\d+) units each with (?P<hit_points>\d+) hit points"
    r" (?:\((?P<weaknesses>.*?)\) )?with an attack that does (?P<damage>\d+)"
    r" (?P<damage_type>\w+) damage at initiative (?P<initiative>\d+)",
)

DAMAGE_MULTIPLIERS = {
    "immune": 0,
    "weak": 2,
}


class InfiniteLoop(Exception):
    pass


@attrs
class Group:
    faction = attrib()
    index = attrib()
    unit_count = attrib(converter=int)
    hit_points = attrib(converter=int)
    weaknesses = attrib()
    damage = attrib(converter=int)
    damage_type = attrib()
    initiative = attrib(converter=int)

    @classmethod
    def from_line(cls, faction, index, line):
        match = GROUP_RE.match(line)
        weaknesses = {}
        if match["weaknesses"]:
            for s in match["weaknesses"].split("; "):
                type_, _, types = s.partition(" to ")
                for damage_type in types.split(", "):
                    weaknesses[damage_type] = DAMAGE_MULTIPLIERS[type_]
        return cls(
            faction=faction,
            index=index,
            unit_count=match["unit_count"],
            hit_points=match["hit_points"],
            weaknesses=weaknesses,
            damage=match["damage"],
            damage_type=match["damage_type"],
            initiative=match["initiative"],
        )

    @property
    def effective_power(self):
        return self.unit_count * self.damage

    def effective_damage(self, other):
        return self.effective_power * other.damage_multiplier(self.damage_type)

    def damage_multiplier(self, damage_type):
        return self.weaknesses.get(damage_type, 1)

    def attack(self, other):
        old_unit_count = other.unit_count
        damage = self.effective_damage(other)
        units_killed = damage // other.hit_points
        other.unit_count -= min(units_killed, old_unit_count)
        return old_unit_count != other.unit_count


def parse_input(filename):
    with open(filename) as input_file:
        text = input_file.read().strip()

    immune_system, infection = text.split("\n\n")
    return (
        [
            Group.from_line("immune_system", i, line)
            for i, line in enumerate(immune_system.splitlines()[1:], 1)
        ],
        [
            Group.from_line("infection", i, line)
            for i, line in enumerate(infection.splitlines()[1:], 1)
        ],
    )


def target_selection(immune_system, infection):
    immune_system = list(immune_system)
    infection = list(infection)
    target_selection_order = sorted(
        immune_system + infection,
        key=attrgetter("effective_power", "initiative"),
        reverse=True,
    )
    targets = []

    for group in target_selection_order:
        opponents = immune_system if group.faction == "infection" else infection
        try:
            opponent = max(
                opponents,
                key=lambda opponent: (
                    group.effective_damage(opponent),
                    opponent.effective_power,
                    opponent.initiative,
                ),
            )
        except ValueError:
            pass
        else:
            if group.effective_damage(opponent):
                targets.append((group, opponent))
                opponents.remove(opponent)

    return targets


def fight(targets, immune_system, infection):
    targets.sort(key=lambda fight: fight[0].initiative, reverse=True)
    any_units_killed = False
    for attacker, defender in targets:
        if attacker.unit_count > 0:
            any_units_killed |= attacker.attack(defender)
    immune_system = [group for group in immune_system if group.unit_count > 0]
    infection = [group for group in infection if group.unit_count > 0]
    return any_units_killed, immune_system, infection


def simulate_combat(filename, *, boost=0):
    immune_system, infection = parse_input(filename)
    for group in immune_system:
        group.damage += boost

    while immune_system and infection:
        targets = target_selection(immune_system, infection)
        any_units_killed, immune_system, infection = fight(targets, immune_system, infection)
        if not any_units_killed:
            raise InfiniteLoop

    return (
        sum(group.unit_count for group in immune_system),
        sum(group.unit_count for group in infection),
    )


def part_2(filename):
    def key(boost, *, filename):
        try:
            immune_system_alive, infection_alive = simulate_combat(filename, boost=boost)
        except InfiniteLoop:
            return False
        assert bool(immune_system_alive) ^ bool(infection_alive)
        return bool(immune_system_alive)

    boost = bisect_left(range(1_000_000_000), True, key=partial(key, filename=filename))
    return sum(simulate_combat(filename, boost=boost))


def test_part_1():
    assert sum(simulate_combat("input_test")) == 5216


def test_part_2():
    assert part_2("input_test") == 51


def main():
    print(sum(simulate_combat("input")))
    print(part_2("input"))


if __name__ == "__main__":
    main()
