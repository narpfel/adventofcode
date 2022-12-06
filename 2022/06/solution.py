#!/usr/bin/env python3

from more_itertools import windowed

EXPECTED_PART_1 = 6
EXPECTED_PART_2 = 23

WINDOW_LENGTH_PART_1 = 4
WINDOW_LENGTH_PART_2 = 14


def read_input(filename):
    with open(filename) as lines:
        return lines.read().strip()


def solve(puzzle_input, start_of_package_marker_length):
    for i, window in enumerate(windowed(puzzle_input, start_of_package_marker_length)):
        if len(set(window)) == start_of_package_marker_length:
            return i + start_of_package_marker_length


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input, WINDOW_LENGTH_PART_1) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input, WINDOW_LENGTH_PART_2) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(solve(puzzle_input, start_of_package_marker_length=WINDOW_LENGTH_PART_1))
    print(solve(puzzle_input, start_of_package_marker_length=WINDOW_LENGTH_PART_2))


if __name__ == "__main__":
    main()
