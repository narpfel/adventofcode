#!/usr/bin/env python3

import re
from collections import deque
from functools import partial
from itertools import chain
from operator import and_
from operator import or_
from operator import xor

import z3

EXPECTED_PART_1 = 2024


class Wire:
    def __init__(self, name, input):
        self.name = name
        self._input = None
        self.outputs = []
        self.input = input

    @property
    def input(self):
        return self._input

    @input.setter
    def input(self, value):
        match self._input:
            case LogicFunction():
                self._input.x.outputs.remove(self)
                self._input.y.outputs.remove(self)

        self._input = value

        match value:
            case LogicFunction():
                value.x.outputs.append(self)
                value.y.outputs.append(self)

    @property
    def transitive_inputs(self):
        try:
            yield self.input.x
        except AttributeError:
            pass
        else:
            yield from self.input.x.transitive_inputs

        try:
            yield self.input.y
        except AttributeError:
            pass
        else:
            yield from self.input.y.transitive_inputs

    @property
    def direct_neighbours(self):
        yield from self.outputs

        try:
            yield self.input.x
        except AttributeError:
            pass

        try:
            yield self.input.y
        except AttributeError:
            pass

    @property
    def surroundings(self):
        seen = set()
        todo = deque()
        todo.append(self)
        while todo:
            wire = todo.popleft()
            yield wire
            seen.add(wire)
            todo.extend(neighbour for neighbour in wire.direct_neighbours if neighbour not in seen)

    def __call__(self):
        return self.input.get()


class LogicFunction:
    def __init__(self, operator, x, y):
        self.operator = operator
        self.x = x
        self.y = y

    def get(self):
        return self.operator(self.x(), self.y())


LOGIC_FUNCTIONS = {
    "AND": partial(LogicFunction, and_),
    "OR": partial(LogicFunction, or_),
    "XOR": partial(LogicFunction, xor),
}


class InputValue:
    def __init__(self):
        self.value = 0
        self.bit_getter = lambda value, bit: (value >> bit) & 1

    def get_bit(self, bit):
        return self.bit_getter(self.value, bit)


class Input:
    def __init__(self, value, bit):
        self.value = value
        self.bit = bit

    def get(self):
        return self.value.get_bit(self.bit)


INSTRUCTION = re.compile(r"((?P<lhs>\w*) (?P<op>\w*) (?P<rhs>\w*)) -> (?P<destination>\w*)")

WIRE_NAME = re.compile(r"[a-z0-9]{3}")


def read_input(filename):
    with open(filename) as lines:
        inputs_lines, instructions = lines.read().strip().split("\n\n")

    wires = {}
    for name in WIRE_NAME.findall(instructions):
        wires[name] = Wire(name, None)

    for line in instructions.splitlines():
        match = INSTRUCTION.match(line)
        wires[match["destination"]].input = LOGIC_FUNCTIONS[match["op"]](
            wires[match["lhs"]],
            wires[match["rhs"]],
        )

    inputs = dict(x=InputValue(), y=InputValue())

    for input_line in inputs_lines.splitlines():
        name, _, bit_value = input_line.partition(": ")
        bit = int(name[1:])
        input_value = inputs[name[0]]
        input_value.value |= int(bit_value) << bit
        wires[name].input = Input(input_value, bit)

    return wires, inputs


def part_1(wires):
    zs = sorted((wire for wire in wires if wire.startswith("z")), reverse=True)
    return int("".join(str(wires[wire]()) for wire in zs), 2)


def swap(wires, lhs, rhs):
    wires[lhs].input, wires[rhs].input = wires[rhs].input, wires[lhs].input


class Correct(BaseException):
    pass


def check_adder(wires, x, y, z, xs_len, zs_len, start_bit):
    x_bits = 2 ** xs_len - 1

    for i in range(start_bit, zs_len):
        solver = z3.Solver()
        solver.add(
            z3.Not(
                z3.Implies(
                    z == (x & x_bits) + (y & x_bits),
                    z3.Extract(i, i, z) == wires[f"z{i:02}"](),
                ),
            ),
        )
        if solver.check() == z3.sat:
            return i

    raise Correct


def part_2(wires, inputs):
    xs, ys, zs = ([wire for wire in wires if wire.startswith(letter)] for letter in "xyz")
    xs_len = len(xs)
    assert xs_len == len(ys)
    zs_len = len(zs)
    assert zs_len == xs_len + 1

    x, y, z = z3.BitVecs("x y z", zs_len)

    for (bit_vec, input_value) in [(x, inputs["x"]), (y, inputs["y"])]:
        input_value.value = bit_vec
        input_value.bit_getter = lambda value, bit: z3.Extract(bit, bit, value)

    swaps = []
    start_bit = max_okay_bit = check_adder(wires, x, y, z, xs_len, zs_len, start_bit=0)
    try:
        while True:
            seen = []
            for wire in wires[f"z{max_okay_bit:02}"].surroundings:
                should_break = False
                for other in seen:
                    if wire in other.transitive_inputs or other in wire.transitive_inputs:
                        continue
                    swaps.append((wire.name, other.name))
                    swap(wires, wire.name, other.name)
                    result = check_adder(wires, x, y, z, xs_len, zs_len, max(0, start_bit - 1))
                    if result > max_okay_bit:
                        start_bit = max_okay_bit
                        max_okay_bit = result
                        should_break = True
                        break
                    swaps.pop()
                    swap(wires, wire.name, other.name)
                seen.append(wire)
                if should_break:
                    break
            else:
                assert False
    except Correct:
        pass

    return ",".join(sorted(chain.from_iterable(swaps)))


def test_part_1():
    wires, _ = read_input("input_test")
    assert part_1(wires) == EXPECTED_PART_1


def main():
    wires, inputs = read_input("input")
    print(part_1(wires))
    print(part_2(wires, inputs))


if __name__ == "__main__":
    main()
