#!/usr/bin/env python3

import re
from string import digits as DIGITS

from more_itertools import flatten

EXPECTED_PART_1 = 142
EXPECTED_PART_2 = 281

DIGITS_AND_WORD_DIGITS = (
    "zero_not_included one two three four five six seven eight nine "
    "0_not_included 1 2 3 4 5 6 7 8 9"
).split()

DIGITS_RE = re.compile("|".join(f"(?=({digit}))" for digit in DIGITS_AND_WORD_DIGITS))


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(lines):
    result = 0
    for line in lines:
        digits = list(map(int, filter(lambda c: c in DIGITS, line)))
        result += 10 * digits[0] + digits[-1]
    return result


def part_2(lines):
    result = 0
    for line in lines:
        digits = list(filter(bool, flatten(DIGITS_RE.findall(line))))
        result += (
            10 * (DIGITS_AND_WORD_DIGITS.index(digits[0]) % 10)
            + (DIGITS_AND_WORD_DIGITS.index(digits[-1]) % 10)
        )
    return result


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test_2")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
