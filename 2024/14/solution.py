#!/usr/bin/env python3

import re
from collections import Counter
from itertools import count
from itertools import product
from math import prod

EXPECTED_PART_1 = 12

ROBOT_RE = re.compile(r"p=(-?\d+),(-?\d+) v=(-?\d+),(-?\d+)")


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            match = ROBOT_RE.fullmatch(line.strip())
            yield (
                (int(match[1]), int(match[2])),
                (int(match[3]), int(match[4])),
            )


def get_quadrants(size_x, size_y):
    yield product(range(size_x // 2), range(size_y // 2))
    yield product(range(size_x // 2), range(size_y // 2 + 1, size_y))
    yield product(range(size_x // 2 + 1, size_x), range(size_y // 2))
    yield product(range(size_x // 2 + 1, size_x), range(size_y // 2 + 1, size_y))


def part_1(robots, *, size_x=101, size_y=103):
    for _ in range(100):
        robots = [
            (
                ((x + vx) % size_x, (y + vy) % size_y),
                (vx, vy),
            )
            for (x, y), (vx, vy) in robots
        ]

    robot_positions = Counter(p for p, _ in robots)

    return prod(
        sum(robot_positions[p] for p in quadrant)
        for quadrant in get_quadrants(size_x, size_y)
    )


def part_2(robots, size_x=101, size_y=103):
    # determined manually
    horizontal_alignment_offset = 31
    vertical_alignment_offset = 68
    for i in count(max(horizontal_alignment_offset, vertical_alignment_offset) + 1):
        if (
            (i - horizontal_alignment_offset) % size_y == 0
            and (i - vertical_alignment_offset) % size_x == 0
        ):
            return i


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input, size_x=11, size_y=7) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
