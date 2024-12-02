#!/usr/bin/env python3

from itertools import pairwise

EXPECTED_PART_1 = 2
EXPECTED_PART_2 = 4


def read_input(filename):
    with open(filename) as lines:
        return [[int(part) for part in line.split()] for line in lines]


def all_increasing(numbers):
    return all(a < b for a, b in pairwise(numbers))


def all_decreasing(numbers):
    return all(a > b for a, b in pairwise(numbers))


def part_1(lines):
    return sum(
        all(abs(a - b) <= 3 for a, b in pairwise(line))
        and (all_decreasing(line) or all_increasing(line))
        for line in lines
    )


def part_2(lines):
    return sum(
        any(part_1([line[:i] + line[i + 1:]]) for i in range(len(line)))
        for line in lines
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    numbers = read_input("input")
    print(part_1(numbers))
    print(part_2(numbers))


if __name__ == "__main__":
    main()
