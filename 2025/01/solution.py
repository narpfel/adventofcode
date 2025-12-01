#!/usr/bin/env python3

EXPECTED_PART_1 = 3


def read_input(filename):
    with open(filename) as lines:
        return [int(line[1:]) * (-1 if line[0] == "L" else 1) for line in lines]


def part_1(rotations):
    position = 50
    stopped_at_zero = 0
    for rotation in rotations:
        position += rotation
        position %= 100
        stopped_at_zero += position == 0
    return stopped_at_zero


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    rotations = read_input("input")
    print(part_1(rotations))


if __name__ == "__main__":
    main()
