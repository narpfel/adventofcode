#!/usr/bin/env python3

from itertools import combinations
from functools import reduce
from operator import mul


def calculate_paper(dimensions):
    sides = [x * y for x, y in combinations(dimensions, 2)]
    return 2 * sum(sides) + min(sides)


def calculate_ribbon(dimensions):
    dimensions = sorted(dimensions)
    return 2 * sum(dimensions[:2]) + reduce(mul, dimensions)


def solve(solver):
    with open("input") as lines:
        return sum(
            solver(
                map(int, line.split("x"))
            )
            for line in lines
        )


def main():
    print(solve(calculate_paper))
    print(solve(calculate_ribbon))


if __name__ == "__main__":
    main()
