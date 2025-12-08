#!/usr/bin/env python3

import math
from itertools import takewhile
from itertools import zip_longest

EXPECTED_PART_1 = 4277556
EXPECTED_PART_2 = 3263827

OPERATORS = {"+": sum, "*": math.prod}


def read_input(filename):
    with open(filename) as input_file:
        return input_file.read().splitlines()


def transpose(xss, fillvalue=" "):
    return zip_longest(*xss, fillvalue=fillvalue)


def part_1(problems):
    return sum(
        OPERATORS[op](map(int, numbers))
        for *numbers, op in transpose(line.split() for line in problems)
    )


def part_2(problems):
    numbers = map("".join, transpose(problems[:-1]))
    operators = problems[-1]
    return sum(
        OPERATORS[op](map(int, takewhile(lambda col: not col.isspace(), numbers)))
        for op in operators.split()
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    problems = read_input("input")
    print(part_1(problems))
    print(part_2(problems))


if __name__ == "__main__":
    main()
