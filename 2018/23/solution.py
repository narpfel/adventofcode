#!/usr/bin/env python3

import re
from operator import attrgetter

NANOBOT_RE = re.compile(r"pos=<(-?\d+),(-?\d+),(-?\d+)>, r=(\d+)")


class Nanobot:
    def __init__(self, position, radius):
        self.position = position
        self.radius = radius

    @classmethod
    def parse(cls, line):
        match = NANOBOT_RE.match(line)
        assert match is not None, line
        return cls((int(match[1]), int(match[2]), int(match[3])), int(match[4]))

    def distance_to(self, other):
        return sum(abs(a - b) for a, b in zip(self.position, other.position))


def read_input(filename):
    with open(filename) as lines:
        return [Nanobot.parse(line) for line in lines]


def part_1(nanobots):
    nanobot = max(nanobots, key=attrgetter("radius"))
    return sum(other.distance_to(nanobot) <= nanobot.radius for other in nanobots)


def test_part_1():
    assert part_1(read_input("input_test")) == 7


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
