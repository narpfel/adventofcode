#!/usr/bin/env pypy3

import re
from enum import IntEnum
from enum import auto
from functools import cache
from heapq import heappop
from heapq import heappush

INPUT_RE = re.compile(
    r"""
depth: (?P<depth>\d+)
target: (?P<x>\d+),(?P<y>\d+)
    """.strip(),
)


class Tool(IntEnum):
    Torch = auto()
    ClimbingGear = auto()
    Empty = auto()


class RiskLevel(IntEnum):
    Rocky = 0
    Wet = 1
    Narrow = 2


TOOLS_FOR_RISK_LEVEL = {
    RiskLevel.Rocky: frozenset({Tool.Torch, Tool.ClimbingGear}),
    RiskLevel.Wet: frozenset({Tool.ClimbingGear, Tool.Empty}),
    RiskLevel.Narrow: frozenset({Tool.Torch, Tool.Empty}),
}


class Cave:
    def __init__(self, target, depth):
        self.target = target
        self.depth = depth

    def risk_level(self, x, y):
        return risk_level(x, y, self.target, self.depth)

    def __getitem__(self, point):
        return self.risk_level(*point)


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


def part_1(cave):
    return sum(
        cave[x, y]
        for x in range(cave.target[0] + 1)
        for y in range(cave.target[1] + 1)
    )


def is_walkable(point):
    x, y = point
    return x >= 0 and y >= 0


def neighbours(point):
    x, y = point
    return [
        (x - 1, y),
        (x, y - 1),
        (x + 1, y),
        (x, y + 1),
    ]


def part_2(cave):
    distance_prev = {}
    next_points = []
    heappush(next_points, (0, (0, 0), Tool.Torch))

    while next_points:
        distance, point, tool = heappop(next_points)

        if (point, tool) == (cave.target, Tool.Torch):
            return distance

        for neighbour in (neighbour for neighbour in neighbours(point) if is_walkable(neighbour)):
            tools = TOOLS_FOR_RISK_LEVEL[cave[point]] & TOOLS_FOR_RISK_LEVEL[cave[neighbour]]
            for next_tool in tools:
                next_distance = distance + 1 + (0 if tool == next_tool else 7)
                if (
                    (neighbour, next_tool) not in distance_prev
                    or distance_prev[neighbour, next_tool][0] > next_distance
                ):
                    distance_prev[neighbour, next_tool] = next_distance, point, tool
                    heappush(next_points, (next_distance, neighbour, next_tool))

    raise AssertionError("unreachable")


def test_part_1():
    assert part_1(Cave(target=(10, 10), depth=510)) == 114


def test_part_2():
    assert part_2(Cave(target=(10, 10), depth=510)) == 45


def main():
    with open("input") as file:
        match = INPUT_RE.match(file.read().strip())

    depth = int(match["depth"])
    x = int(match["x"])
    y = int(match["y"])

    cave = Cave(target=(x, y), depth=depth)
    print(part_1(cave))
    print(part_2(cave))


if __name__ == "__main__":
    main()
