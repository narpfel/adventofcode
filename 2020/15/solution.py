#!/usr/bin/env pypy3

from collections import defaultdict
from itertools import count

import pytest

INPUT = "16,12,1,0,15,7,11"


def parse_input(starting_numbers):
    return [int(n) for n in starting_numbers.split(",")]


def solve(starting_numbers, turn_count):
    number_to_turns = defaultdict(
        list,
        zip(starting_numbers, map(lambda turn: [turn], count())),
    )
    last_spoken = starting_numbers[-1]

    for turn in range(len(starting_numbers), turn_count):
        spoken_on = number_to_turns[last_spoken]
        if len(spoken_on) == 1:
            last_spoken = 0
        else:
            last_spoken = spoken_on[-1] - spoken_on[-2]
        number_to_turns[last_spoken].append(turn)

    return last_spoken


@pytest.mark.parametrize(
    "starting_numbers, count, expected", [
        ("0,3,6", 2020, 436),
        ("1,3,2", 2020, 1),
        ("2,1,3", 2020, 10),
        ("1,2,3", 2020, 27),
        ("2,3,1", 2020, 78),
        ("3,2,1", 2020, 438),
        ("3,1,2", 2020, 1836),
        ("0,3,6", 30000000, 175594),
        ("1,3,2", 30000000, 2578),
        ("2,1,3", 30000000, 3544142),
        ("1,2,3", 30000000, 261214),
        ("2,3,1", 30000000, 6895259),
        ("3,2,1", 30000000, 18),
        ("3,1,2", 30000000, 362),
    ],
)
def test_solve(starting_numbers, count, expected):
    assert solve(parse_input(starting_numbers), count) == expected


def main():
    print(solve(parse_input(INPUT), 2020))
    print(solve(parse_input(INPUT), 30000000))


if __name__ == "__main__":
    main()
