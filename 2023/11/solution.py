#!/usr/bin/env pypy3

from collections import namedtuple
from itertools import combinations

EXPECTED_PART_1 = 374

Universe = namedtuple("Universe", "galaxies, empty_x, empty_y")


def read_input(filename):
    with open(filename) as lines:
        galaxies = {
            (x, y)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
            if c == "#"
        }
    max_x = max(x for x, _ in galaxies)
    max_y = max(y for _, y in galaxies)
    empty_x = {
        x
        for x in range(max_x + 1)
        if not any((x, y) in galaxies for y in range(max_y + 1))
    }
    empty_y = {
        y
        for y in range(max_y + 1)
        if not any((x, y) in galaxies for x in range(max_x + 1))
    }
    return Universe(galaxies, empty_x, empty_y)


def distances_stretched(universe, stretch):
    return sum(
        abs(x - X) + abs(y - Y)
        + stretch * (
            sum(a in universe.empty_x for a in range(min(x, X), max(x, X)))
            + sum(a in universe.empty_y for a in range(min(y, Y), max(y, Y)))
        )
        for (x, y), (X, Y) in combinations(universe.galaxies, r=2)
    )


def part_1(universe):
    return distances_stretched(universe, 1)


def part_2(universe):
    return distances_stretched(universe, 1_000_000 - 1)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert distances_stretched(puzzle_input, 10 - 1) == 1030
    assert distances_stretched(puzzle_input, 100 - 1) == 8410


def main():
    universe = read_input("input")
    print(part_1(universe))
    print(part_2(universe))


if __name__ == "__main__":
    main()
