#!/usr/bin/env python3

import re
from functools import partial
from operator import and_
from operator import or_
from operator import xor

EXPECTED_PART_1 = 2024


class Wire:
    def __init__(self, name, input):
        self.input = input

    def __call__(self):
        try:
            return int(self.input)
        except TypeError:
            try:
                return self.input()
            except TypeError:
                return self.input


def logic_function(operator, x, y):
    return operator(x(), y())


LOGIC_FUNCTIONS = {
    "AND": partial(logic_function, and_),
    "OR": partial(logic_function, or_),
    "XOR": partial(logic_function, xor),
}

INSTRUCTION = re.compile(r"((?P<lhs>\w*) (?P<op>\w*) (?P<rhs>\w*)) -> (?P<destination>\w*)")

WIRE_NAME = re.compile(r"[a-z0-9]{3}")


def read_input(filename):
    with open(filename) as lines:
        inputs, instructions = lines.read().strip().split("\n\n")

    wires = {}
    for name in WIRE_NAME.findall(instructions):
        wires[name] = Wire(name, None)

    for input_line in inputs.splitlines():
        name, _, value = input_line.partition(": ")
        wires[name].input = int(value)

    for line in instructions.splitlines():
        match = INSTRUCTION.match(line)
        wires[match["destination"]].input = partial(
            LOGIC_FUNCTIONS[match["op"]],
            wires[match["lhs"]],
            wires[match["rhs"]],
        )

    return wires


def part_1(wires):
    zs = sorted((wire for wire in wires if wire.startswith("z")), reverse=True)
    return int("".join(str(wires[wire]()) for wire in zs), 2)


def test_part_1():
    wires = read_input("input_test")
    assert part_1(wires) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
