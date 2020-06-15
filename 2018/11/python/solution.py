#!/usr/bin/env pypy3
from collections import namedtuple
from itertools import chain
from operator import attrgetter

GRID_SIZE = 300

INPUT = 7672


Window = namedtuple("Window", "x, y, window_size, total_power")


def windowed(grid, window_size):
    y = len(grid)
    x = len(grid[0])
    for i in range(1, x - window_size):
        for j in range(1, y - window_size):
            a = grid[j][i]
            b = grid[j][i + window_size]
            c = grid[j + window_size][i + window_size]
            d = grid[j + window_size][i]
            power_level = c + a - d - b
            yield Window(i + 1, j + 1, window_size, power_level)


def power_level(x, y, serial_number):
    rack_id = x + 10
    return ((((rack_id * y + serial_number) * rack_id) // 100) % 10) - 5


def calculate_power_level(serial_number):
    return [
        [power_level(x, y, serial_number) for x in range(GRID_SIZE + 1)]
        for y in range(GRID_SIZE + 1)
    ]


def precompute_sums(grid):
    for line in grid:
        for x in range(1, len(line)):
            line[x] += line[x - 1]
    for y in range(1, len(grid)):
        for x in range(len(grid[y])):
            grid[y][x] += grid[y - 1][x]


def solve(power_levels, window_sizes):
    return max(
        chain.from_iterable(
            windowed(power_levels, window_size)
            for window_size in window_sizes
        ),
        key=attrgetter("total_power")
    )


def main():
    power_levels = calculate_power_level(INPUT)
    precompute_sums(power_levels)
    x, y, _, _ = solve(power_levels, [3])
    print(f"{x},{y}")
    x, y, window_size, _ = solve(power_levels, range(1, GRID_SIZE + 1))
    print(f"{x},{y},{window_size}")


if __name__ == "__main__":
    main()
