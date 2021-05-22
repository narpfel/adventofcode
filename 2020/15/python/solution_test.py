#!/usr/bin/env pypy3

import pytest
from solution import parse_input
from solution import solve


@pytest.mark.parametrize(
    "starting_numbers, count, expected", [
        ("0,3,6", 2020, 436),
        ("1,3,2", 2020, 1),
        ("2,1,3", 2020, 10),
        ("1,2,3", 2020, 27),
        ("2,3,1", 2020, 78),
        ("3,2,1", 2020, 438),
        ("3,1,2", 2020, 1836),
        ("0,3,6", 30_000_000, 175594),
        ("1,3,2", 30_000_000, 2578),
        ("2,1,3", 30_000_000, 3544142),
        ("1,2,3", 30_000_000, 261214),
        ("2,3,1", 30_000_000, 6895259),
        ("3,2,1", 30_000_000, 18),
        ("3,1,2", 30_000_000, 362),
    ],
)
def test_solve(starting_numbers, count, expected):
    assert solve(parse_input(starting_numbers), count) == expected
