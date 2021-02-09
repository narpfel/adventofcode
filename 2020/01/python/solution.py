#!/usr/bin/env python3

from itertools import combinations
from math import prod

import pytest


def read_input(filename):
    with open(filename) as lines:
        return list(map(int, lines))


def solve(expenses, length):
    for values in combinations(expenses, length):
        if sum(values) == 2020:
            return prod(values)


@pytest.mark.parametrize(
    "length, expected",
    [
        pytest.param(2, 514579, id="part 1"),
        pytest.param(3, 241861950, id="part 2"),
    ],
)
def test(length, expected):
    assert solve(read_input("input_test"), length) == expected


def main():
    expenses = sorted(read_input("input"))
    print(solve(expenses, 2))
    print(solve(expenses, 3))


if __name__ == "__main__":
    main()
