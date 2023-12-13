#!/usr/bin/env python3

from operator import eq

EXPECTED_PART_1 = 405
EXPECTED_PART_2 = 400


def read_input(filename):
    with open(filename) as lines:
        return [chunk.splitlines() for chunk in lines.read().split("\n\n")]


def transpose(xss):
    return list(zip(*xss))


def find_row_of_reflection(lines, *, key=lambda xs, ys: all(map(eq, xs, ys))):
    for y in range(1, len(lines)):
        if key(reversed(lines[:y]), lines[y:]):
            return y
    return 0


def part_1(patterns):
    rows = sum(find_row_of_reflection(chunk) for chunk in patterns)
    cols = sum(find_row_of_reflection(transpose(chunk)) for chunk in patterns)
    return 100 * rows + cols


def count_inequalities(xss, yss):
    return sum(x != y for xs, ys in zip(xss, yss) for x, y in zip(xs, ys, strict=True))


def exactly_one_inequality(xs, ys):
    return count_inequalities(xs, ys) == 1


def part_2(patterns):
    rows = sum(
        find_row_of_reflection(chunk, key=exactly_one_inequality)
        for chunk in patterns
    )
    cols = sum(
        find_row_of_reflection(transpose(chunk), key=exactly_one_inequality)
        for chunk in patterns
    )
    return 100 * rows + cols


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    patterns = read_input("input")
    print(part_1(patterns))
    print(part_2(patterns))


if __name__ == "__main__":
    main()
