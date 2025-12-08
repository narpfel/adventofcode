#!/usr/bin/env python3

import math
from itertools import combinations

EXPECTED_PART_1 = 40


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(coordinate) for coordinate in line.split(",")) for line in lines]


def distance_squared(points):
    return sum((x1 - x2) ** 2 for x1, x2 in zip(*points))


def part_1(junction_boxes, *, to_connect):
    distances = sorted(
        ((p1, p2) for p1, p2 in combinations(junction_boxes, r=2)),
        key=distance_squared,
        reverse=True,
    )
    circuits = {p: {p} for p in junction_boxes}

    for _ in range(to_connect):
        p1, p2 = distances.pop()
        connected_circuit = circuits[p1] | circuits[p2]
        for p in connected_circuit:
            circuits[p] = connected_circuit

    sizes = sorted(len(c) for c in {frozenset(c) for c in circuits.values()})
    return math.prod(sizes[-3:])


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input, to_connect=10) == EXPECTED_PART_1


def main():
    junction_boxes = read_input("input")
    print(part_1(junction_boxes, to_connect=1000))


if __name__ == "__main__":
    main()
