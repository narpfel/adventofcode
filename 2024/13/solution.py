#!/usr/bin/env python3

import re
from functools import partial

EXPECTED_PART_1 = 480

NUMBER_RE = re.compile(r"\d+")

A_LOT = 10000000000000


def read_input(filename):
    with open(filename) as lines:
        for chunk in lines.read().split("\n\n"):
            ax, ay, bx, by, px, py = NUMBER_RE.findall(chunk)
            yield (
                (int(ax), int(ay)),
                (int(bx), int(by)),
                (int(px), int(py)),
            )


def calculate_cost(machine, *, offset):
    (ax, ay), (bx, by), (px, py) = machine
    px += offset
    py += offset
    numerator = ax * py - ay * px
    denominator = ax * by - ay * bx
    if numerator % denominator == 0:
        button_b_presses = numerator // denominator
        numerator = px - button_b_presses * bx
        if numerator % ax == 0:
            button_a_presses = numerator // ax
            assert button_a_presses > 0
            assert button_b_presses > 0
            return 3 * button_a_presses + button_b_presses

    return None


def calculate_total_cost(machines, *, offset):
    return sum(filter(None, map(partial(calculate_cost, offset=offset), machines)))


def part_1(machines):
    return calculate_total_cost(machines, offset=0)


def part_2(machines):
    return calculate_total_cost(machines, offset=A_LOT)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    machines = list(read_input("input"))
    print(part_1(machines))
    print(part_2(machines))


if __name__ == "__main__":
    main()
