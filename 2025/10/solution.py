#!/usr/bin/env python3

from collections import namedtuple
from functools import reduce
from itertools import product
from operator import mul
from operator import xor

EXPECTED_PART_1 = 7


Machine = namedtuple("Machine", "lights, buttons")


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            lights, *buttons, _joltage_requirements = line.split()
            yield Machine(
                lights=sum((light == "#") << i for i, light in enumerate(lights[1:-1])),
                buttons=[
                    sum(1 << int(connection) for connection in button[1:-1].split(","))
                    for button in buttons
                ],
            )


def part_1(machines):
    return sum(
        min(
            sum(is_button_activated)
            for is_button_activated in product([0, 1], repeat=len(machine.buttons))
            if machine.lights == reduce(xor, map(mul, machine.buttons, is_button_activated))
        )
        for machine in machines
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    machines = list(read_input("input"))
    print(part_1(machines))


if __name__ == "__main__":
    main()
