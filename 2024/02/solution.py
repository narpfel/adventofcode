#!/usr/bin/env python3

from more_itertools import windowed

EXPECTED_PART_1 = 2


def read_input(filename):
    with open(filename) as lines:
        return [[int(part) for part in line.split()] for line in lines]


def all_increasing(numbers):
    return all(a < b for a, b in windowed(numbers, 2))


def all_decreasing(numbers):
    return all(a > b for a, b in windowed(numbers, 2))


def part_1(lines):
    return sum(
        all(abs(a - b) <= 3 for a, b in windowed(line, 2))
        and (all_decreasing(line) or all_increasing(line))
        for line in lines
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
