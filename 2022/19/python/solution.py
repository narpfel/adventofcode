#!/usr/bin/env pypy3

import math
import re
from typing import NamedTuple

BLUEPRINT_RE = re.compile(
    r"Blueprint (?P<id>\d+): "
    r"Each ore robot costs (?P<ore_robot_ore>\d+) ore. "
    r"Each clay robot costs (?P<clay_robot_ore>\d+) ore. "
    r"Each obsidian robot costs (?P<obsidian_robot_ore>\d+) ore "
    r"and (?P<obsidian_robot_clay>\d+) clay. "
    r"Each geode robot costs (?P<geode_robot_ore>\d+) ore "
    r"and (?P<geode_robot_obsidian>\d+) obsidian.",
)


class Materials(NamedTuple):
    ore: int = 0
    clay: int = 0
    obsidian: int = 0

    def can_afford(self, other):
        return (
            self.ore >= other.ore
            and self.clay >= other.clay
            and self.obsidian >= other.obsidian
            # if we can afford two, we probably could have afforded the cost last minute
            and not (
                self.ore >= 2 * other.ore
                and self.clay >= 2 * other.clay
                and self.obsidian >= 2 * other.obsidian
            )
        )


class Blueprint(NamedTuple):
    id: int
    ore_robot: Materials
    clay_robot: Materials
    obsidian_robot: Materials
    geode_robot: Materials

    @classmethod
    def parse(cls, line):
        match = BLUEPRINT_RE.match(line)
        assert match is not None
        return cls(
            id=int(match["id"]),
            ore_robot=Materials(ore=int(match["ore_robot_ore"])),
            clay_robot=Materials(ore=int(match["clay_robot_ore"])),
            obsidian_robot=Materials(
                ore=int(match["obsidian_robot_ore"]),
                clay=int(match["obsidian_robot_clay"]),
            ),
            geode_robot=Materials(
                ore=int(match["geode_robot_ore"]),
                obsidian=int(match["geode_robot_obsidian"]),
            ),
        )

    def quality_level(self):
        return self.max_geodes(24) * self.id

    def max_geodes(self, time_limit):
        states = [State()]
        max_geodes = 0

        while states:
            state = states.pop()
            if state.time == time_limit:
                max_geodes = max(max_geodes, state.geodes)
            else:
                new_state = state.step()
                if state.can_afford(self.geode_robot):
                    states.append(
                        new_state
                        .spend(self.geode_robot)
                        ._replace(geode_robots=new_state.geode_robots + 1),
                    )
                else:
                    states.append(new_state)
                    if state.can_afford(self.ore_robot):
                        states.append(
                            new_state
                            .spend(self.ore_robot)
                            ._replace(ore_robots=new_state.ore_robots + 1),
                        )
                    if state.can_afford(self.clay_robot):
                        states.append(
                            new_state
                            .spend(self.clay_robot)
                            ._replace(clay_robots=new_state.clay_robots + 1),
                        )
                    if state.can_afford(self.obsidian_robot):
                        states.append(
                            new_state
                            .spend(self.obsidian_robot)
                            ._replace(obsidian_robots=new_state.obsidian_robots + 1),
                        )

        return max_geodes


class State(NamedTuple):
    time: int = 0
    geodes: int = 0
    geode_robots: int = 0
    obsidian: int = 0
    obsidian_robots: int = 0
    clay: int = 0
    clay_robots: int = 0
    ore: int = 0
    ore_robots: int = 1

    def step(self):
        return self._replace(
            time=self.time + 1,
            ore=self.ore + self.ore_robots,
            clay=self.clay + self.clay_robots,
            obsidian=self.obsidian + self.obsidian_robots,
            geodes=self.geodes + self.geode_robots,
        )

    @property
    def materials(self):
        return Materials(
            ore=self.ore,
            clay=self.clay,
            obsidian=self.obsidian,
        )

    def can_afford(self, materials):
        return self.materials.can_afford(materials) and not (
            # if all of these are true, we definitely could have
            # afforded the cost last minute
            materials.ore <= self.ore - self.ore_robots
            and materials.clay <= self.clay - self.clay_robots
            and materials.obsidian <= self.obsidian - self.obsidian_robots
        )

    def spend(self, materials):
        return self._replace(
            ore=self.ore - materials.ore,
            clay=self.clay - materials.clay,
            obsidian=self.obsidian - materials.obsidian,
        )


def read_input(filename):
    with open(filename) as lines:
        return [Blueprint.parse(line) for line in lines]


def part_1(blueprints):
    return sum(blueprint.quality_level() for blueprint in blueprints)


def part_2(blueprints):
    return math.prod(blueprint.max_geodes(32) for blueprint in blueprints[:3])


def test_part_1():
    blueprints = read_input("input_test")
    assert blueprints[0].quality_level() == 9
    assert blueprints[1].quality_level() == 24


def test_part_2():
    blueprints = read_input("input_test")
    assert blueprints[0].max_geodes(32) == 56
    assert blueprints[1].max_geodes(32) == 62


def main():
    blueprints = read_input("input")
    print(part_1(blueprints))
    print(part_2(blueprints))


if __name__ == "__main__":
    main()
