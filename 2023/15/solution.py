#!/usr/bin/env python3

EXPECTED_PART_1 = 1320


def read_input(filename):
    with open(filename) as lines:
        return lines.read().strip().split(",")


def calculate_hash(s):
    hash_value = 0
    for c in s:
        hash_value += ord(c)
        hash_value *= 17
        hash_value %= 256
    return hash_value


def part_1(initialisation_sequence):
    return sum(calculate_hash(step) for step in initialisation_sequence)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    initialisation_sequence = read_input("input")
    print(part_1(initialisation_sequence))


if __name__ == "__main__":
    main()
