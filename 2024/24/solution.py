#!/usr/bin/env python3

import re
from collections import deque
from functools import cache
from functools import partial
from itertools import chain
from operator import and_
from operator import or_
from operator import xor

EXPECTED_PART_1 = 2024

INSTRUCTION = re.compile(r"((?P<lhs>\w*) (?P<op>\w*) (?P<rhs>\w*)) -> (?P<destination>\w*)")
WIRE_NAME = re.compile(r"[a-z0-9]{3}")

# unsure if this works for all inputs
TEST_CASES = [
    (0xffff_ffff_ffff_ffff, 1),
    (0xffff_ffff_ffff_ffff, 0),
    (1, 0xffff_ffff_ffff_ffff),
    (0, 0xffff_ffff_ffff_ffff),
]


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

    @cache
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

    def get_bit(self, bit):
        return (self.value >> bit) & 1


class Input:
    def __init__(self, value, bit):
        self.value = value
        self.bit = bit

    def get(self):
        return self.value.get_bit(self.bit)


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


def check_adder(wires, x, y, zs_len):
    mask = 2 ** (zs_len - 1) - 1
    first_error_bit = zs_len + 1

    for (x_value, y_value) in TEST_CASES:
        Wire.__call__.cache_clear()
        x.value = x_value & mask
        y.value = y_value & mask
        expected_z = x.value + y.value
        actual_z = part_1(wires)

        for i in range(zs_len):
            if ((expected_z >> i) & 1) != ((actual_z >> i) & 1):
                first_error_bit = min(i, first_error_bit)
                break

    if first_error_bit <= zs_len:
        return first_error_bit
    else:
        raise Correct


def lazy_combinations(iterable):
    seen = set()
    for value in iterable:
        if value not in seen:
            for other in seen:
                yield value, other
            seen.add(value)


def part_2(wires, inputs):
    xs, ys, zs = ([wire for wire in wires if wire.startswith(letter)] for letter in "xyz")
    xs_len = len(xs)
    assert xs_len == len(ys)
    zs_len = len(zs)
    assert zs_len == xs_len + 1

    swaps = []
    first_error_bit = check_adder(wires, **inputs, zs_len=zs_len)
    try:
        while True:
            for wire, other in lazy_combinations(wires[f"z{first_error_bit:02}"].surroundings):
                if wire in other.transitive_inputs or other in wire.transitive_inputs:
                    continue
                swaps.append((wire.name, other.name))
                swap(wires, wire.name, other.name)
                error_bit = check_adder(wires, **inputs, zs_len=zs_len)
                if error_bit > first_error_bit:
                    first_error_bit = error_bit
                    break
                swaps.pop()
                swap(wires, wire.name, other.name)
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
