#!/usr/bin/env python3

from collections import namedtuple
from itertools import chain
from operator import attrgetter

import numpy as np


GRID_SIZE = 300

INPUT = 7672


Window = namedtuple("Window", "x, y, window_size, total_power")


def windowed(array, window_size):
    y, x = array.shape
    for i in range(1, x - window_size + 1):
        for j in range(1, y - window_size + 1):
            yield Window(i, j, window_size, array[i:i + window_size, j:j + window_size].sum())


def calculate_power_level(serial_number):
    x = np.arange(GRID_SIZE + 1)
    y = np.arange(GRID_SIZE + 1)
    rack_id = x + 10
    power_level = np.outer(rack_id, y) + serial_number
    power_level = (power_level.T * rack_id).T
    power_level //= 100
    power_level %= 10
    power_level -= 5
    return power_level


def solve(serial_number, window_sizes):
    return max(
        chain.from_iterable(
            windowed(calculate_power_level(serial_number), window_size)
            for window_size in window_sizes
        ),
        key=attrgetter("total_power")
    )


def main():
    x, y, _, _ = solve(INPUT, [3])
    print(f"{x},{y}")
    x, y, window_size, _ = solve(INPUT, range(1, GRID_SIZE + 1))
    print(f"{x},{y},{window_size}")


if __name__ == "__main__":
    main()
