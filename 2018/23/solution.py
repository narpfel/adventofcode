#!/usr/bin/env python3

import re
from operator import attrgetter

import z3

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


def manhattan_distance(p1, p2):
    return z3.Sum([z3.Abs(a - b) for a, b in zip(p1, p2)])


def part_2(nanobots):
    opt = z3.Optimize()
    point = z3.Int("p0"), z3.Int("p1"), z3.Int("p2")
    in_range = [
        z3.If(manhattan_distance(point, nanobot.position) <= nanobot.radius, 1, 0)
        for nanobot in nanobots
    ]
    opt.maximize(z3.Sum(in_range))
    opt.minimize(manhattan_distance(point, (0, 0, 0)))
    assert opt.check() == z3.sat
    model = opt.model()
    return sum(abs(model[x].as_long()) for x in point)


def test_part_1():
    assert part_1(read_input("input_test")) == 7


def test_part_2():
    assert part_2(read_input("input_test_2")) == 36


def main():
    nanobots = read_input("input")
    print(part_1(nanobots))
    print(part_2(nanobots))


if __name__ == "__main__":
    main()
