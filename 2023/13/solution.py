#!/usr/bin/env python3

from operator import eq

EXPECTED_PART_1 = 405


def read_input(filename):
    with open(filename) as lines:
        return [chunk.splitlines() for chunk in lines.read().split("\n\n")]


def transpose(xss):
    return list(zip(*xss))


def find_row_of_reflection(lines):
    for y in range(1, len(lines)):
        if all(map(eq, reversed(lines[:y]), lines[y:])):
            return y
    return 0


def part_1(patterns):
    rows = sum(find_row_of_reflection(chunk) for chunk in patterns)
    cols = sum(find_row_of_reflection(transpose(chunk)) for chunk in patterns)
    return 100 * rows + cols


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    patterns = read_input("input")
    print(part_1(patterns))


if __name__ == "__main__":
    main()
