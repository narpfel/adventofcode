#!/usr/bin/env python3

from itertools import chain

EXPECTED_PART_1 = 18
EXPECTED_PART_2 = 9


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


def count_x_mas(lines):
    transposed_lines = list(transpose(lines))

    a_positions = [
        (y, x)
        for y, line in enumerate(lines)
        for x, c in enumerate(line)
        if c == "A"
    ]

    return sum(
        lines[y][x-1:x+2] in ("MAS", "SAM") and transposed_lines[x][y-1:y+2] in ("MAS", "SAM")
        for y, x in a_positions
    )


def part_2(lines):
    return sum(map(count_x_mas, rotate_45_degrees(lines)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
