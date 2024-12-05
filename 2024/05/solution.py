#!/usr/bin/env python3

from functools import cmp_to_key
from itertools import pairwise

EXPECTED_PART_1 = 143
EXPECTED_PART_2 = 123


def read_input(filename):
    with open(filename) as lines:
        orderings, updates = lines.read().split("\n\n")
        return (
            frozenset(tuple(int(s) for s in line.split("|")) for line in orderings.splitlines()),
            [[int(s) for s in line.split(",")] for line in updates.splitlines()],
        )


def part_1(puzzle_input):
    orderings, updates = puzzle_input
    return sum(
        update[len(update) // 2]
        for update in updates
        if not any((b, a) in orderings for a, b in pairwise(update))
    )


def part_2(puzzle_input):
    orderings, updates = puzzle_input
    key = cmp_to_key(lambda a, b: 1 if (a, b) in orderings else -1)
    return sum(
        sorted(update, key=key)[len(update) // 2]
        for update in updates
        if any((b, a) in orderings for a, b in pairwise(update))
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
