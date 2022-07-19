#!/usr/bin/env python3

import re
from collections import namedtuple
from itertools import product

STEP_RE = re.compile(
    r"(?P<state>on|off) "
    r"x=(?P<x_min>-?\d+)\.\.(?P<x_max>-?\d+),"
    r"y=(?P<y_min>-?\d+)\.\.(?P<y_max>-?\d+),"
    r"z=(?P<z_min>-?\d+)\.\.(?P<z_max>-?\d+)",
)

Step = namedtuple("Step", "state, x, y, z")


def contains(haystack, needle):
    assert haystack.step == 1
    assert needle.step == 1
    return haystack.start <= needle.start and needle.stop <= haystack.stop


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


def solve(steps):
    region = range(-50, 51)
    reactor = {
        (x, y, z): False
        for x, y, z in product(region, repeat=3)
    }

    for step in steps:
        if contains(region, step.x) and contains(region, step.y) and contains(region, step.z):
            for coord in product(step.x, step.y, step.z):
                reactor[coord] = step.state

    return sum(reactor.values())


def test():
    assert solve(read_input("input_test_1")) == 39
    assert solve(read_input("input_test_2")) == 590784


def main():
    steps = read_input("input")
    print(solve(steps))


if __name__ == "__main__":
    main()
