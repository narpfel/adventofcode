#!/usr/bin/env python3

import re

EXPECTED_PART_1 = 161

MULTIPLICATIONS_RE = re.compile(r"mul\((\d+),(\d+)\)")


def read_input(filename):
    with open(filename) as lines:
        return lines.read().strip()


def part_1(code):
    return sum(
        int(match[1]) * int(match[2])
        for match in MULTIPLICATIONS_RE.finditer(code)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    code = read_input("input")
    print(part_1(code))


if __name__ == "__main__":
    main()
