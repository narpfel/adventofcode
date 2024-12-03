#!/usr/bin/env python3

import re

EXPECTED_PART_1 = 161
EXPECTED_PART_2 = 48

MULTIPLICATIONS_RE = re.compile(r"mul\((\d+),(\d+)\)")
MULTIPLICATIONS_DO_DONT_RE = re.compile(r"mul\((\d+),(\d+)\)|do\(\)|don't\(\)")


def read_input(filename):
    with open(filename) as lines:
        return lines.read().strip()


def part_1(code):
    return sum(
        int(match[1]) * int(match[2])
        for match in MULTIPLICATIONS_RE.finditer(code)
    )


def part_2(code):
    matches = MULTIPLICATIONS_DO_DONT_RE.finditer(code)
    is_enabled = True
    result = 0
    for match in matches:
        match match[0]:
            case "do()":
                is_enabled = True
            case "don't()":
                is_enabled = False
            case _ if is_enabled:
                result += int(match[1]) * int(match[2])
    return result


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test_2")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    code = read_input("input")
    print(part_1(code))
    print(part_2(code))


if __name__ == "__main__":
    main()
