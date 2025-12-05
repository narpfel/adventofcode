#!/usr/bin/env python3

import sys

sys.path.insert(0, "../../2016")
sparse = __import__("20.solution").solution

EXPECTED_PART_1 = 3
EXPECTED_PART_2 = 14


def read_input(filename):
    with open(filename) as lines:
        ranges, ids = lines.read().strip().split("\n\n")
        return (
            [tuple(map(int, range.split("-"))) for range in ranges.splitlines()],
            list(map(int, ids.splitlines())),
        )


def part_1(ranges, ids):
    return sum(
        any(id in range(lo, hi + 1) for lo, hi in ranges)
        for id in ids
    )


def part_2(ranges):
    combined_ranges = []
    for lo, hi in ranges:
        sparse.insert(combined_ranges, (lo, hi))
    return sparse.length(combined_ranges)


def test_part_1():
    ranges, ids = read_input("input_test")
    assert part_1(ranges, ids) == EXPECTED_PART_1


def test_part_2():
    ranges, _ = read_input("input_test")
    assert part_2(ranges) == EXPECTED_PART_2


def main():
    ranges, ids = read_input("input")
    print(part_1(ranges, ids))
    print(part_2(ranges))


if __name__ == "__main__":
    main()
