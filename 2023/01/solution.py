#!/usr/bin/env python3

from string import digits as DIGITS

EXPECTED_PART_1 = 142


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(lines):
    result = 0
    for line in lines:
        digits = list(map(int, filter(lambda c: c in DIGITS, line)))
        result += 10 * digits[0] + digits[-1]
    return result


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
