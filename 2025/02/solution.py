#!/usr/bin/env python3

import re

EXPECTED_PART_1 = 1227775554


def read_input(filename):
    with open(filename) as ranges:
        return [
            tuple(map(int, id_range.split("-")))
            for id_range in ranges.read().strip().split(",")
        ]


def sum_invalid_ids(ranges, pattern):
    pattern = re.compile(pattern)
    return sum(
        i
        for lo, hi in ranges
        for i in range(lo, hi + 1)
        if pattern.fullmatch(str(i))
    )


def part_1(ranges):
    return sum_invalid_ids(ranges, r"(.+)\1")


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    ranges = read_input("input")
    print(part_1(ranges))


if __name__ == "__main__":
    main()
