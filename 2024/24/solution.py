#!/usr/bin/env python3

import re
import sys
from functools import partial
from itertools import chain
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


def part_2(wires, *, check):
    # solved semi-manually using a `dot` plot of the addition circuit and `z3`
    # to indicate the location of the first wrong output bit
    #
    # swaps:
    # srp, jcf (is: z05, must: frn) <-> kbj, qjq (is: frn, must: z05)
    # x16, y16 (is: wnf, must: vtj) <-> x16, y16 (is: vtj, must: wnf)
    # x21, y21 (is: z21, must: gmq) <-> fqr, mjj (is: gmq, must: z21)
    # jhv, bkq (is: z39, must: wtt) <-> jhv, bkq (is: wtt, must: z39)

    swaps = [
        ("z05", "frn"),
        ("wnf", "vtj"),
        ("z21", "gmq"),
        ("z39", "wtt"),
    ]
    for lhs, rhs in swaps:
        wires[lhs].input, wires[rhs].input = wires[rhs].input, wires[lhs].input

    if check:
        import z3

        xs = [wire for wire in wires if wire.startswith("x")]
        ys = [wire for wire in wires if wire.startswith("y")]
        zs = [wire for wire in wires if wire.startswith("z")]
        xs_len = len(xs)
        ys_len = len(ys)
        assert xs_len == ys_len
        zs_len = len(zs)
        assert zs_len == xs_len + 1

        x, y, z = z3.BitVecs("x y z", zs_len)

        for input_number, input_names in zip([x, y], [xs, ys]):
            for name in input_names:
                place = int(name[1:])
                wires[name].input = (input_number >> place) & 1

        x_bits = 2 ** xs_len - 1

        for i in range(zs_len):
            solver = z3.Solver()
            solver.add(
                z3.Not(
                    z3.Implies(
                        z == (x & x_bits) + (y & x_bits),
                        ((z >> i) & 1) == wires[f"z{i:02}"](),
                    ),
                ),
            )
            if solver.check() == z3.sat:
                print(f"counter-example in bit {i}: ", solver.model())
                raise AssertionError(f"swaps are incorrect, error in {i}th bit")

    return ",".join(sorted(chain.from_iterable(swaps)))


def test_part_1():
    wires = read_input("input_test")
    assert part_1(wires) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input"), check="--check" in sys.argv))


if __name__ == "__main__":
    main()
