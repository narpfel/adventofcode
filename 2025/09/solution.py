#!/usr/bin/env python3

from itertools import combinations

EXPECTED_PART_1 = 50


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(part) for part in line.split(",")) for line in lines]


def part_1(points):
    return max(
        (abs(x - X) + 1) * (abs(y - Y) + 1)
        for (x, y), (X, Y) in combinations(points, r=2)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    points = read_input("input")
    print(part_1(points))


if __name__ == "__main__":
    main()
