#!/usr/bin/env python3

import math
import re
from collections import defaultdict
from itertools import product

EXPECTED_PART_1 = 4361
EXPECTED_PART_2 = 467835

SYMBOL_RE = re.compile(r"[^\d\.]")


def read_input(filename):
    with open(filename) as lines:
        lines = list(lines)
    numbers = [
        (j, match)
        for j, line in enumerate(lines)
        for match in re.finditer(r"\d+", line)
    ]
    return lines, numbers


def adjacent_indices(lines, line, span):
    return product(
        range(max(0, line - 1), min(len(lines), line + 2)),
        range(max(0, span[0] - 1), min(len(lines[line]), span[1] + 1)),
    )


def part_1(lines, numbers):
    return sum(
        int(match[0])
        for j, match in numbers
        if any(
            SYMBOL_RE.match(lines[J][I])
            for J, I in adjacent_indices(lines, j, match.span())
        )
    )


def part_2(lines, numbers):
    gears = defaultdict(list)

    for j, match in numbers:
        for J, I in adjacent_indices(lines, j, match.span()):
            if lines[J][I] == "*":
                gears[J, I].append(int(match[0]))

    return sum(
        math.prod(gear)
        for gear in gears.values()
        if len(gear) == 2
    )


def test_part_1():
    lines, numbers = read_input("input_test")
    assert part_1(lines, numbers) == EXPECTED_PART_1


def test_part_2():
    lines, numbers = read_input("input_test")
    assert part_2(lines, numbers) == EXPECTED_PART_2


def main():
    lines, numbers = read_input("input")
    print(part_1(lines, numbers))
    print(part_2(lines, numbers))


if __name__ == "__main__":
    main()
