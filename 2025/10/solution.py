#!/usr/bin/env python3

from collections import namedtuple
from functools import reduce
from itertools import product
from operator import mul
from operator import xor
from string import ascii_uppercase

import z3

EXPECTED_PART_1 = 7
EXPECTED_PART_2 = 33


Machine = namedtuple("Machine", "lights, buttons, button_connections, joltage_requirements")


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            lights, *buttons, joltage_requirements = line.split()
            yield Machine(
                lights=sum((light == "#") << i for i, light in enumerate(lights[1:-1])),
                buttons=[
                    sum(1 << int(connection) for connection in button[1:-1].split(","))
                    for button in buttons
                ],
                button_connections=[
                    [int(connection) for connection in button[1:-1].split(",")]
                    for button in buttons
                ],
                joltage_requirements=[
                    int(joltage)
                    for joltage in joltage_requirements[1:-1].split(",")
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


def configure_joltage_levels(machine):
    solver = z3.Optimize()
    buttons = [z3.Int(c) for c in ascii_uppercase[:len(machine.buttons)]]
    for count in buttons:
        solver.add(count >= 0)

    for i, joltage in enumerate(machine.joltage_requirements):
        conntected_buttons = (
            buttons[k]
            for k, connections in enumerate(machine.button_connections)
            if i in connections
        )
        solver.add(joltage == z3.Sum(conntected_buttons))

    result = z3.Sum(buttons)
    solver.minimize(result)
    assert solver.check() == z3.sat
    model = solver.model()
    return model.evaluate(result).as_long()


def part_2(machines):
    return sum(configure_joltage_levels(machine) for machine in machines)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    machines = list(read_input("input"))
    print(part_1(machines))
    print(part_2(machines))


if __name__ == "__main__":
    main()
