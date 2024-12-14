#!/usr/bin/env python3

import re
from collections import Counter
from functools import reduce
from itertools import count
from itertools import product
from math import prod
from operator import iand
from operator import ior

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


def step(robots, size_x, size_y):
    return [
        (
            ((x + vx) % size_x, (y + vy) % size_y),
            (vx, vy),
        )
        for (x, y), (vx, vy) in robots
    ]


def predict_robot_motion(steps, robots, *, size_x, size_y):
    robots = list(robots)
    yield robots
    for _ in range(steps):
        robots = step(robots, size_x, size_y)
        yield robots


def part_1(robots, *, size_x=101, size_y=103):
    robot_positions = Counter(p for p, _ in robots[100])

    return prod(
        sum(robot_positions[p] for p in quadrant)
        for quadrant in get_quadrants(size_x, size_y)
    )


def part_2(robots, size_x=101, size_y=103):
    max_horizontal_correlation_at = 0, 0
    max_vertical_correlation_at = 0, 0
    for i, robots_after_step in enumerate(robots):
        if i in range(size_x):
            max_vertical_correlation_at = max(max_vertical_correlation_at, (
                len(reduce(ior, (
                    reduce(iand, (
                        {(x, y + dy) for (x, y), _ in robots_after_step}
                        for dy in (0, dy)
                    ))
                    for dy in (-1, 1)
                ))),
                i,
            ))
        if i in range(size_y):
            max_horizontal_correlation_at = max(max_horizontal_correlation_at, (
                len(reduce(ior, (
                    reduce(iand, (
                        {(x + dx, y) for (x, y), _ in robots_after_step}
                        for dx in (0, dx)
                    ))
                    for dx in (-1, 1)
                ))),
                i,
            ))

    _, horizontal_alignment_offset = max_horizontal_correlation_at
    _, vertical_alignment_offset = max_vertical_correlation_at

    for i in count(max(horizontal_alignment_offset, vertical_alignment_offset) + 1):
        if (
            (i - horizontal_alignment_offset) % size_y == 0
            and (i - vertical_alignment_offset) % size_x == 0
        ):
            return i


def test_part_1():
    puzzle_input = read_input("input_test")
    robots = list(predict_robot_motion(100, puzzle_input, size_x=11, size_y=7))
    assert part_1(robots, size_x=11, size_y=7) == EXPECTED_PART_1


def main():
    initial_robots = read_input("input")
    robots = list(predict_robot_motion(103, initial_robots, size_x=101, size_y=103))
    print(part_1(robots))
    print(part_2(robots))


if __name__ == "__main__":
    main()
