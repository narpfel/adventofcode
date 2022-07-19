#!/usr/bin/env pypy3

import re
from collections import Counter
from collections import namedtuple

STEP_RE = re.compile(
    r"(?P<state>on|off) "
    r"x=(?P<x_min>-?\d+)\.\.(?P<x_max>-?\d+),"
    r"y=(?P<y_min>-?\d+)\.\.(?P<y_max>-?\d+),"
    r"z=(?P<z_min>-?\d+)\.\.(?P<z_max>-?\d+)",
)

Step = namedtuple("Step", "state, x, y, z")


class Cuboid(namedtuple("Rectangle", "top_left, bottom_right")):
    def __bool__(self):
        return (
            self.top_left[0] <= self.bottom_right[0]
            and self.top_left[1] <= self.bottom_right[1]
            and self.top_left[2] <= self.bottom_right[2]
        )

    @property
    def size(self):
        size = (
            (self.bottom_right[0] - self.top_left[0] + 1)
            * (self.bottom_right[1] - self.top_left[1] + 1)
            * (self.bottom_right[2] - self.top_left[2] + 1)
        )
        assert size > 0
        return size

    def overlap(self, other):
        top_left = (
            max(self.top_left[0], other.top_left[0]),
            max(self.top_left[1], other.top_left[1]),
            max(self.top_left[2], other.top_left[2]),
        )
        bottom_right = (
            min(self.bottom_right[0], other.bottom_right[0]),
            min(self.bottom_right[1], other.bottom_right[1]),
            min(self.bottom_right[2], other.bottom_right[2]),
        )
        return Cuboid(top_left, bottom_right)


PART_1_REGION = Cuboid((-50, -50, -50), (50, 50, 50))


def read_input(filename):
    steps = []
    with open(filename) as lines:
        for line in lines:
            match = STEP_RE.match(line)
            assert match is not None
            steps.append(
                Step(
                    state=match["state"] == "on",
                    x=range(int(match["x_min"]), int(match["x_max"]) + 1),
                    y=range(int(match["y_min"]), int(match["y_max"]) + 1),
                    z=range(int(match["z_min"]), int(match["z_max"]) + 1),
                ),
            )

    return steps


def solve(steps, *, region=None):
    cuboids = Counter()
    for step in steps:
        top_left = min(step.x), min(step.y), min(step.z)
        bottom_right = max(step.x), max(step.y), max(step.z)
        cuboid = Cuboid(top_left, bottom_right)
        assert cuboid, cuboid
        new_cuboids = Counter()
        for (other, count) in cuboids.items():
            overlap = cuboid.overlap(other)
            if overlap:
                new_cuboids[overlap] -= count
        if step.state:
            cuboids[cuboid] += 1
        cuboids.update(new_cuboids)

    return sum(
        cuboid.size * count
        for cuboid, count in cuboids.items()
        if region is None or cuboid.overlap(region)
    )


def main():
    steps = read_input("input")
    print(solve(steps, region=PART_1_REGION))
    print(solve(steps))


if __name__ == "__main__":
    main()
