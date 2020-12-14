#!/usr/bin/env python3

import re
from collections import defaultdict

MEM_RE = re.compile(r"^mem\[(?P<address>\d+)\] = (?P<value>\d+)$")


def main():
    with open("input") as lines:
        instructions = [line for line in lines]

    memory = defaultdict(int)
    set_bits = 0
    unset_bits = 2 ** 36 - 1
    for instruction in instructions:
        if instruction.startswith("mask"):
            _, _, mask = instruction.strip().partition(" = ")
            set_bits = int("".join("1" if bit == "1" else "0" for bit in mask), 2)
            unset_bits = int("".join("1" if bit == "0" else "0" for bit in mask), 2)
        elif instruction.startswith("mem"):
            match = MEM_RE.match(instruction)
            if match is None:
                raise ValueError(f"invalid instruction: {instruction!r}")
            memory[int(match["address"])] = (int(match["value"]) | set_bits) & ~unset_bits
        else:
            raise ValueError(f"invalid instruction: {instruction!r}")
    print(sum(memory.values()))


if __name__ == "__main__":
    main()
