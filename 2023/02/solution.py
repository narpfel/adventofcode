#!/usr/bin/env python3

import math
from collections import Counter

EXPECTED_PART_1 = 8
EXPECTED_PART_2 = 2286


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            game, handfuls = line.split(":")
            game_id = int(game.split()[-1])
            yield game_id, [
                Counter({
                    colour: int(count)
                    for count, colour in map(str.split, handful.split(", "))
                })
                for handful in handfuls.split("; ")
            ]


def part_1(games):
    return sum(
        game_id
        for game_id, counts in games
        if all(c < Counter({"red": 12, "green": 13, "blue": 14}) for c in counts)
    )


def part_2(games):
    return sum(
        math.prod(
            max(c.get(colour) for c in counts if c.get(colour))
            for colour in ("red", "green", "blue")
        )
        for _, counts in games
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
