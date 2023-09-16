#!/usr/bin/env python3

from __future__ import annotations

from collections.abc import Iterable
from itertools import cycle
from typing import TypeVar

import cython
from cython import long
from cython import ulong

T = TypeVar("T")


# declare `DICE` as global because `pyupgrade` crashes on arrays of tuples in
# type annotations and `cython.locals` doesn’t seem to work?
cython.declare(DICE=(ulong, ulong)[7])
DICE = [(3, 1), (4, 3), (5, 6), (6, 7), (7, 6), (8, 3), (9, 1)]


class Player:
    def __init__(self, position: ulong, name: ulong) -> None:
        self.name = name
        self.position = position - 1
        self.score = 0

    def roll(self, roll: ulong) -> None:
        self.position = (self.position + roll) % 10
        self.score += self.position + 1


def read_input(filename: str) -> list[Player]:
    with open(filename) as lines:
        return [Player(int(line.split()[-1]), i) for i, line in enumerate(lines)]


def chunked(xs: Iterable[T], n: long) -> Iterable[tuple[T, ...]]:
    xs = iter(xs)
    return zip(*[xs] * n)


def rolls(dice):
    for xs in chunked(dice, 3):
        yield sum(xs)


def part_1(players: list[Player]) -> ulong:
    die = cycle(range(1, 101))
    for i, (player, roll) in enumerate(zip(cycle(players), rolls(die)), 1):
        player.roll(roll)
        if player.score >= 1000:
            break

    return i * 3 * min(player.score for player in players)


@cython.cfunc
def part_2(
    n1: ulong, n2: ulong,
    p1: ulong, p2: ulong,
    s1: ulong, s2: ulong,
    n: ulong = 1,
) -> tuple[ulong, ulong]:
    r1: ulong = 0
    r2: ulong = 0
    i: ulong
    for i in range(7):
        roll: ulong = DICE[i][0]
        multiplicity: ulong = DICE[i][1]
        position: ulong = (p1 + roll) % 10
        score: ulong = s1 + position + 1
        if score >= 21:
            if n1 == 0:
                r1 += multiplicity * n
            else:
                r2 += multiplicity * n
        else:
            results: tuple[ulong, ulong]
            results = part_2(n2, n1, p2, position, s2, score, n=n * multiplicity)
            r1 += results[0]
            r2 += results[1]
    return (r1, r2)


@cython.cfunc
@cython.locals(dice=(ulong, ulong)[7])
def cmain():
    print(part_1(read_input("input")))

    p1, p2 = read_input("input")
    result = part_2(0, 1, p1.position, p2.position, 0, 0)
    print(max(result))


def main():
    cmain()


if __name__ == "__main__":
    main()
