#!/usr/bin/env python3

from collections import defaultdict
from itertools import cycle


def make_santa(gifts):
    x, y = 0, 0

    def decode_move(direction):
        nonlocal x, y
        if direction == "^":
            y += 1
        elif direction == "v":
            y -= 1
        elif direction == "<":
            x -= 1
        elif direction == ">":
            x += 1
        gifts[(x, y)] += 1

    return decode_move


def walk_houses(directions, santa_count):
    x, y = 0, 0
    gifts = defaultdict(int)
    gifts[(x, y)] += 1

    santas = [make_santa(gifts) for _ in range(santa_count)]

    directions = iter(directions)
    for direction, santa in zip(directions, cycle(santas)):
        santa(direction)
    return len(gifts)


def main():
    with open("input") as lines:
        directions = next(lines)

    print(walk_houses(directions, 1))
    print(walk_houses(directions, 2))


if __name__ == '__main__':
    main()
