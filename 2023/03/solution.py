#!/usr/bin/env python3

import re
from itertools import product

EXPECTED_PART_1 = 4361

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


def test_part_1():
    lines, numbers = read_input("input_test")
    assert part_1(lines, numbers) == EXPECTED_PART_1


def main():
    lines, numbers = read_input("input")
    print(part_1(lines, numbers))


if __name__ == "__main__":
    main()
