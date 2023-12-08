#!/usr/bin/env python3

import math
import re
from itertools import cycle

EXPECTED_PART_1 = 6
EXPECTED_PART_2 = 6


def read_input(filename):
    with open(filename) as lines:
        instrs, nodes = lines.read().split("\n\n")
        node_connections = {}
        for node in nodes.splitlines():
            node, connections = node.split(" = ")
            left, right = re.findall(r"\w\w\w", connections)
            node_connections[node] = left, right
        return [0 if i == "L" else 1 for i in instrs.strip()], node_connections


def part_1(instrs, nodes, *, node="AAA", is_at_end=lambda n: n == "ZZZ"):
    for i, instr in enumerate(cycle(instrs), 1):
        node = nodes[node][instr]
        if is_at_end(node):
            return i


def part_2(instrs, nodes):
    return math.lcm(
        *(
            part_1(instrs, nodes, node=node, is_at_end=lambda n: n.endswith("Z"))
            for node in nodes
            if node.endswith("A")
        ),
    )


def test_part_1():
    instrs, nodes = read_input("input_test")
    assert part_1(instrs, nodes) == EXPECTED_PART_1


def test_part_2():
    instrs, nodes = read_input("input_test_2")
    assert part_2(instrs, nodes) == EXPECTED_PART_2


def main():
    instrs, nodes = read_input("input")
    print(part_1(instrs, nodes))
    print(part_2(instrs, nodes))


if __name__ == "__main__":
    main()
