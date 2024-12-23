#!/usr/bin/env python3

from collections import defaultdict
from itertools import combinations

EXPECTED_PART_1 = 7


def read_input(filename):
    with open(filename) as lines:
        connections = defaultdict(set)
        for line in lines:
            a, b = line.strip().split("-")
            connections[a].add(b)
            connections[b].add(a)
        return connections


def part_1(connections):
    return sum(
        1
        for c1, c2, c3 in combinations(connections, r=3)
        if (
            c1 in connections[c2]
            and c1 in connections[c3]
            and c2 in connections[c1]
            and c2 in connections[c3]
            and c3 in connections[c1]
            and c3 in connections[c2]
            and (
                c1.startswith("t")
                or c2.startswith("t")
                or c3.startswith("t")
            )
        )
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    connections = read_input("input")
    print(part_1(connections))


if __name__ == "__main__":
    main()
