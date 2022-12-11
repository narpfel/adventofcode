#!/usr/bin/env python3

import re
from collections import Counter
from functools import partial
from operator import add
from operator import mul

from attr import attrib
from attr import attrs

EXPECTED_PART_1 = 10605

MONKEY_RE = re.compile(
    r"""
Monkey (?P<number>\d+):
  Starting items: (?P<starting_items>.*)
  Operation: new = old (?P<operator>[+*]) ((?P<operation_number>\d+)|(?P<operation_old>old))
  Test: divisible by (?P<test_number>\d+)
    If true: throw to monkey (?P<target_if_true>\d+)
    If false: throw to monkey (?P<target_if_false>\d+)
""".strip(),
)

OPERATIONS = {"+": add, "*": mul}


@attrs
class Monkey:
    number = attrib()
    items = attrib()
    operation = attrib()
    test_number = attrib()
    target_if_true = attrib()
    target_if_false = attrib()

    @classmethod
    def parse(cls, text):
        match = MONKEY_RE.match(text)
        assert match is not None
        operator = OPERATIONS[match["operator"]]
        if match["operation_number"] is not None:
            operation = partial(operator, int(match["operation_number"]))
        elif match["operation_old"] is not None:
            def operation(old):
                return operator(old, old)
        else:
            assert False, "unreachable"
        return cls(
            number=int(match["number"]),
            items=list(map(int, match["starting_items"].split(", "))),
            operation=operation,
            test_number=int(match["test_number"]),
            target_if_true=int(match["target_if_true"]),
            target_if_false=int(match["target_if_false"]),
        )

    def test(self, worry_level):
        return worry_level % self.test_number == 0

    @property
    def target(self):
        return [self.target_if_false, self.target_if_true]


def read_input(filename):
    with open(filename) as file:
        return [Monkey.parse(part) for part in file.read().split("\n\n")]


def part_1(monkeys):
    item_inspections = Counter()
    for _ in range(20):
        for monkey in monkeys:
            items = monkey.items
            monkey.items = []
            for item in items:
                item_inspections[monkey.number] += 1
                worry_level = monkey.operation(item)
                worry_level //= 3
                target = monkey.target[monkey.test(worry_level)]
                assert target != monkey.number
                monkeys[target].items.append(worry_level)

    most_active = item_inspections.most_common(2)
    return most_active[0][1] * most_active[1][1]


def test_part_1():
    monkeys = read_input("input_test")
    assert part_1(monkeys) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
