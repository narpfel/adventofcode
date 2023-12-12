#!/usr/bin/env python3

from collections import namedtuple
from itertools import combinations

EXPECTED_PART_1 = 374

Universe = namedtuple("Universe", "galaxies, empty_x, empty_y")


def cumsum(xs):
    acc = 0
    for x in xs:
        acc += x
        yield acc


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
    empty_x = list(
        cumsum(
            not any((x, y) in galaxies for y in range(max_y + 1))
            for x in range(max_x + 1)
        ),
    )
    empty_y = list(
        cumsum(
            not any((x, y) in galaxies for x in range(max_x + 1))
            for y in range(max_y + 1)
        ),
    )
    return Universe(galaxies, empty_x, empty_y)


def distances_stretched(universe, stretch):
    return sum(
        abs(x - X) + abs(y - Y)
        + stretch * (
            universe.empty_x[max(x, X)] - universe.empty_x[min(x, X)]
            + universe.empty_y[max(y, Y)] - universe.empty_y[min(y, Y)]
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
