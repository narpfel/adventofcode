#!/usr/bin/env python3

EXPECTED_PART_1 = 3


def read_input(filename):
    with open(filename) as lines:
        ranges, ids = lines.read().strip().split("\n\n")
        ranges = [range.split("-") for range in ranges.splitlines()]
        return (
            [range(int(lo), int(hi) + 1) for lo, hi in ranges],
            list(map(int, ids.splitlines())),
        )


def part_1(ranges, ids):
    return sum(
        any(id in range for range in ranges)
        for id in ids
    )


def test_part_1():
    ranges, ids = read_input("input_test")
    assert part_1(ranges, ids) == EXPECTED_PART_1


def main():
    ranges, ids = read_input("input")
    print(part_1(ranges, ids))


if __name__ == "__main__":
    main()
