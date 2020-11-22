#!/usr/bin/env pypy3

import re
from itertools import count

import attr

DISC_RE = re.compile(
    r"Disc #(?P<disc_number>\d+) has (?P<position_count>\d+)"
    r" positions; at time=0, it is at position (?P<start_position>\d+).",
)


@attr.s
class Disc:
    position_count = attr.ib(converter=int)
    position = attr.ib(converter=int)

    @classmethod
    def from_str(cls, s):
        match = DISC_RE.match(s)
        if match is None:
            raise ValueError(f"str does not describe a Disc: {s!r}")

        return cls(position_count=match["position_count"], position=match["start_position"])

    def __iadd__(self, other):
        self.position = (self.position + other) % self.position_count

    def __add__(self, other):
        return type(self)(
            position_count=self.position_count,
            position=(self.position + other) % self.position_count,
        )

    def can_be_passed(self, offset):
        return (self + offset).position == 0


def read_input(filename):
    with open(filename) as lines:
        return [Disc.from_str(line) for line in lines]


def solve(discs):
    for solution in count():
        if all(disc.can_be_passed(i) for i, disc in enumerate(discs, 1)):
            return solution
        for disc in discs:
            disc += 1


def main():
    discs = read_input("input")
    part1 = solve(discs)
    print(part1)

    discs = read_input("input")
    discs.append(Disc(position_count=11, position=0))
    part2 = solve(discs)
    print(part2)


if __name__ == "__main__":
    main()
