#!/usr/bin/env python3

import re
from functools import cache

INPUT_RE = re.compile(
    r"""
depth: (?P<depth>\d+)
target: (?P<x>\d+),(?P<y>\d+)
    """.strip(),
)


def geologic_index(x, y, target, depth):
    if (x, y) == (0, 0):
        return 0
    elif (x, y) == target:
        return 0
    elif y == 0:
        return x * 16807
    elif x == 0:
        return y * 48271
    else:
        assert x > 0 and y > 0, (x, y)
        return erosion_level(x - 1, y, target, depth) * erosion_level(x, y - 1, target, depth)


@cache
def erosion_level(x, y, target, depth):
    return (geologic_index(x, y, target, depth) + depth) % 20183


def risk_level(x, y, target, depth):
    return erosion_level(x, y, target, depth) % 3


def part_1(*, target, depth):
    return sum(
        risk_level(x, y, target, depth)
        for y in range(target[1] + 1)
        for x in range(target[0] + 1)
    )


def test_part_1():
    assert part_1(target=(10, 10), depth=510) == 114


def main():
    with open("input") as file:
        match = INPUT_RE.match(file.read().strip())

    depth = int(match["depth"])
    x = int(match["x"])
    y = int(match["y"])

    print(part_1(target=(x, y), depth=depth))


if __name__ == "__main__":
    main()
