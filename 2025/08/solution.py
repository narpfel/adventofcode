#!/usr/bin/env python3

import math
from itertools import combinations
from itertools import count

EXPECTED_PART_1 = 40
EXPECTED_PART_2 = 25272


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(coordinate) for coordinate in line.split(",")) for line in lines]


def distance_squared(points):
    return sum((x1 - x2) ** 2 for x1, x2 in zip(*points))


def solve(junction_boxes, *, to_connect):
    distances = sorted(
        ((p1, p2) for p1, p2 in combinations(junction_boxes, r=2)),
        key=distance_squared,
        reverse=True,
    )
    circuits = {p: {p} for p in junction_boxes}

    for i in count(1):
        p1, p2 = distances.pop()
        connected_circuit = circuits[p1] | circuits[p2]
        for p in connected_circuit:
            circuits[p] = connected_circuit
        if i == to_connect:
            sizes = sorted(len(c) for c in {frozenset(c) for c in circuits.values()})
            part_1 = math.prod(sizes[-3:])
        if len(next(iter(circuits.values()))) == len(junction_boxes):
            return part_1, p1[0] * p2[0]


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input, to_connect=10)[0] == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input, to_connect=10)[1] == EXPECTED_PART_2


def main():
    junction_boxes = read_input("input")
    part_1, part_2 = solve(junction_boxes, to_connect=1000)
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
