#!/usr/bin/env python3

from itertools import chain

EXPECTED_PART_1 = 18


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def transpose(lines):
    return map("".join, zip(*lines))


def count_xmas(lines):
    return sum(
        line.count("XMAS") + line.count("SAMX")
        for line in chain(lines, transpose(lines))
    )


def rotate_45_degrees(lines):
    assert len(lines) == len(lines[0])
    n = len(lines)
    upper_left = (
        [lines[y][i - y - 1] for y in range(i)]
        for i in range(n + 1)
    )
    bottom_right = (
        reversed([lines[n - j - 1][n - i + j] for j in range(i)])
        for i in reversed(range(n))
    )
    result = ["".join(line).center(n) for line in chain(upper_left, bottom_right)]
    return result[::2], result[1::2]


def part_1(lines):
    return count_xmas(lines) + sum(map(count_xmas, rotate_45_degrees(lines)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
