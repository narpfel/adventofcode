#!/usr/bin/env python3

import re

import numpy as np


COORDINATE_RE = re.compile("<(.*?)>")


def parse(line):
    return list(list(map(int, coord.split(", "))) for coord in COORDINATE_RE.findall(line))


def read_input(filename):
    with open(filename) as lines:
        return np.array([parse(line) for line in lines]).transpose(1, 2, 0)


def area(positions):
    x, y = positions
    return abs(x.max() - x.min()) * abs(y.max() - y.min())


def solve(positions, velocities):
    return min(
        enumerate(positions + i * velocities for i in range(2 * 10 ** 4)),
        key=lambda v: area(v[1]),
    )


def main():
    positions, velocities = read_input("input")
    time, solution_positions = solve(positions, velocities)
    min_x, min_y = solution_positions.min(axis=1)
    max_x, max_y = solution_positions.max(axis=1)

    image = [[" "] * (max_x - min_x + 1) for _ in range(max_y - min_y + 1)]
    for x, y in solution_positions.T:
        image[y - min_y][x - min_x] = "#"

    for line in image:
        print("".join(line))

    print(time)


if __name__ == "__main__":
    main()
