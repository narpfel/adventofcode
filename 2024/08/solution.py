#!/usr/bin/env python3

from collections import defaultdict
from itertools import combinations

EXPECTED_PART_1 = 14
EXPECTED_PART_2 = 34


def read_input(filename):
    with open(filename) as lines:
        lines = [line.strip() for line in lines]

    antenna_locations = defaultdict(list)
    for y, line in enumerate(lines):
        for x, c in enumerate(line):
            if c != ".":
                antenna_locations[c].append((x, y))
    return antenna_locations, len(lines[0]), len(lines)


def solve(puzzle_input, *, offsets):
    def add_nodes_with_offsets(x, y, dx, dy):
        for i in offsets:
            nx = x - dx * i
            ny = y - dy * i
            if nx not in range(max_x) or ny not in range(max_y):
                break
            antinode_locations.add((nx, ny))

    antenna_locations, max_x, max_y = puzzle_input
    antinode_locations = set()
    for antenna_locations_for_type in antenna_locations.values():
        for (x, y), (X, Y) in combinations(antenna_locations_for_type, r=2):
            dx, dy = X - x, Y - y
            add_nodes_with_offsets(x, y, dx, dy)
            add_nodes_with_offsets(X, Y, -dx, -dy)
    return len(antinode_locations)


def part_1(puzzle_input):
    return solve(puzzle_input, offsets=[1])


def part_2(puzzle_input):
    _, max_x, max_y = puzzle_input
    return solve(puzzle_input, offsets=range(max(max_x, max_y)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
