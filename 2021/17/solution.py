#!/usr/bin/env pypy3

import re
from functools import partial
from itertools import count
from itertools import product
from itertools import takewhile


def Δ(n):
    return n * (n + 1) // 2


def x(v_x, t):
    x_max = Δ(v_x)
    return x_max - Δ(max(v_x - t, 0))


def y(v_y, t):
    return v_y * t - Δ(t - 1)


def in_range(x_max, y_min, xy):
    x, y = xy
    return x <= x_max and y_min <= y


def main():
    with open("input") as file:
        target_area = file.read()

    x_min, x_max, y_min, y_max = map(int, re.findall(r"-?\d+", target_area))

    print(Δ(abs(y_min) - 1))

    x_range = range(x_min, x_max + 1)
    y_range = range(y_min, y_max + 1)

    possible_start_velocity_count = sum(
        any(
            x_pos in x_range and y_pos in y_range
            for x_pos, y_pos in takewhile(
                partial(in_range, x_max, y_min),
                ((x(v_x, t), y(v_y, t)) for t in count()),
            )
        )
        for v_x, v_y in product(range(1, x_max + 1), range(y_min, -y_min))
    )
    print(possible_start_velocity_count)


if __name__ == "__main__":
    main()
