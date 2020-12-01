#!/usr/bin/env python3

from functools import reduce
from itertools import combinations
from operator import mul


def solve(expenses, length):
    for values in combinations(expenses, length):
        if sum(values) == 2020:
            return reduce(mul, values)


def main():
    with open("input") as lines:
        expenses = list(map(int, lines))

    print(solve(expenses, 2))
    print(solve(expenses, 3))


if __name__ == "__main__":
    main()
