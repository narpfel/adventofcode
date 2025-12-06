#!/usr/bin/env python3

import math

EXPECTED_PART_1 = 4277556

OPERATORS = {"+": sum, "*": math.prod}


def read_input(filename):
    with open(filename) as input_file:
        return input_file.read().splitlines()


def transpose(xss):
    return zip(*xss)


def part_1(problems):
    return sum(
        OPERATORS[op](map(int, numbers))
        for *numbers, op in transpose(line.split() for line in problems)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    problems = read_input("input")
    print(part_1(problems))


if __name__ == "__main__":
    main()
