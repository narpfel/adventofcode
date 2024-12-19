#!/usr/bin/env pypy3

from functools import cache

EXPECTED_PART_1 = 6
EXPECTED_PART_2 = 16


def read_input(filename):
    with open(filename) as lines:
        patterns, towels = lines.read().split("\n\n")
        return tuple(patterns.strip().split(", ")), towels.strip().splitlines()


@cache
def count_possibilities(patterns, towel):
    if not towel:
        return 1
    else:
        return sum(
            count_possibilities(patterns, towel.removeprefix(pattern))
            for pattern in patterns
            if towel.startswith(pattern)
        )


def part_1(puzzle_input):
    patterns, towels = puzzle_input
    return sum(count_possibilities(patterns, towel) != 0 for towel in towels)


def part_2(puzzle_input):
    patterns, towels = puzzle_input
    return sum(count_possibilities(patterns, towel) for towel in towels)


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
