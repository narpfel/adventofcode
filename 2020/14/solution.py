#!/usr/bin/env python3

import re
from collections import defaultdict
from itertools import product

MEM_RE = re.compile(r"^mem\[(?P<address>\d+)\] = (?P<value>\d+)$")


def parse_mask(mask):
    return (
        int("".join("1" if bit == "1" else "0" for bit in mask), 2),
        int("".join("1" if bit == "0" else "0" for bit in mask), 2),
    )


def solve_part1(instructions):
    memory = defaultdict(int)
    set_bits = 0
    unset_bits = 2 ** 36 - 1
    for instruction in instructions:
        if instruction.startswith("mask"):
            _, _, mask = instruction.strip().partition(" = ")
            set_bits, unset_bits = parse_mask(mask)
        elif instruction.startswith("mem"):
            match = MEM_RE.match(instruction)
            if match is None:
                raise ValueError(f"invalid instruction: {instruction!r}")
            memory[int(match["address"])] = (int(match["value"]) | set_bits) & ~unset_bits
        else:
            raise ValueError(f"invalid instruction: {instruction!r}")
    return sum(memory.values())


def solve_part2(instructions):
    memory = defaultdict(int)
    for instruction in instructions:
        if instruction.startswith("mask"):
            _, _, mask = instruction.strip().partition(" = ")
            floating_mask = ["01" if bit == "X" else "X" for bit in mask]
            set_mask, _ = parse_mask(mask)
        elif instruction.startswith("mem"):
            match = MEM_RE.match(instruction)
            if match is None:
                raise ValueError(f"invalid instruction: {instruction!r}")
            for address_mask in product(*floating_mask):
                set_bits, unset_bits = parse_mask(address_mask)
                memory[
                    (int(match["address"]) | set_bits) & ~unset_bits | set_mask
                ] = int(match["value"])
        else:
            raise ValueError(f"invalid instruction: {instruction!r}")
    return sum(memory.values())


def main():
    with open("input") as lines:
        instructions = [line for line in lines]

    print(solve_part1(instructions))
    print(solve_part2(instructions))


if __name__ == "__main__":
    main()
