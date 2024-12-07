#!/usr/bin/env pypy3

import math
from operator import add
from operator import mul

EXPECTED_PART_1 = 3749
EXPECTED_PART_2 = 11387


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            expected_result, operands = line.split(": ")
            yield int(expected_result), [int(operand) for operand in operands.split()]


def calculate_test_values(operands, operators):
    test_values = [operands[0]]
    for operand in operands[1:]:
        test_values = [
            operator(value, operand)
            for value in test_values
            for operator in operators
        ]
    return test_values


def calculate_total_calibration_result(puzzle_input, operators):
    return sum(
        expected_result
        for expected_result, operands in puzzle_input
        if any(
            test_value == expected_result
            for test_value in calculate_test_values(operands, operators)
        )
    )


def part_1(puzzle_input):
    return calculate_total_calibration_result(puzzle_input, [add, mul])


def concat(x, y):
    y_digit_count = int(math.log10(y)) + 1
    return x * 10**y_digit_count + y


def part_2(puzzle_input):
    return calculate_total_calibration_result(puzzle_input, [add, mul, concat])


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = list(read_input("input"))
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
