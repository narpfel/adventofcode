#!/usr/bin/env python3

from collections import defaultdict
from itertools import combinations

EXPECTED_PART_1 = 14


def read_input(filename):
    with open(filename) as lines:
        lines = [line.strip() for line in lines]

    antenna_locations = defaultdict(list)
    for y, line in enumerate(lines):
        for x, c in enumerate(line):
            if c != ".":
                antenna_locations[c].append((x, y))
    return antenna_locations, len(lines[0]), len(lines)


def part_1(puzzle_input):
    antenna_locations, max_x, max_y = puzzle_input
    antinode_locations = set()
    for antenna_locations_for_type in antenna_locations.values():
        for (x, y), (X, Y) in combinations(antenna_locations_for_type, r=2):
            dx, dy = X - x, Y - y
            antinode_locations.add((x - dx, y - dy))
            antinode_locations.add((X + dx, Y + dy))
    return sum(x in range(max_x) and y in range(max_y) for x, y in antinode_locations)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
