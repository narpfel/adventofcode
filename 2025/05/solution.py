#!/usr/bin/env python3

import sys

sys.path.insert(0, "../../2016")
sparse = __import__("20.solution").solution

EXPECTED_PART_1 = 3
EXPECTED_PART_2 = 14


def read_input(filename):
    with open(filename) as lines:
        ranges, ids = lines.read().strip().split("\n\n")
        combined_ranges = []
        for line in ranges.splitlines():
            lo, hi = line.split("-")
            sparse.insert(combined_ranges, (int(lo), int(hi)))
        return (combined_ranges, list(map(int, ids.splitlines())))


def part_1(ranges, ids):
    return sum(sparse.contains(ranges, id) for id in ids)


def part_2(ranges):
    return sparse.length(ranges)


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
