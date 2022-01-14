#!/usr/bin/env python3

from __future__ import annotations

from collections import Counter
from itertools import cycle
from itertools import product
from typing import Iterable
from typing import TypeVar

T = TypeVar("T")


class Player:
    def __init__(self, position: int, name: int) -> None:
        self.name = name
        self.position = position - 1
        self.score = 0

    def roll(self, roll: int) -> None:
        self.position = (self.position + roll) % 10
        self.score += self.position + 1


def read_input(filename: str) -> list[Player]:
    with open(filename) as lines:
        return [Player(int(line.split()[-1]), i) for i, line in enumerate(lines)]


def chunked(xs: Iterable[T], n: int) -> Iterable[tuple[T, ...]]:
    xs = iter(xs)
    return zip(*[xs] * n)


def rolls(dice: Iterable[int]) -> Iterable[int]:
    for xs in chunked(dice, 3):
        yield sum(xs)


def part_1(players: list[Player]) -> int:
    die = cycle(range(1, 101))
    for i, (player, roll) in enumerate(zip(cycle(players), rolls(die)), 1):
        player.roll(roll)
        if player.score >= 1000:
            break

    return i * 3 * min(player.score for player in players)


# removing all abstractions improves performance by ~15x on PyPy
def part_2(
    n1: int, n2: int,
    p1: int, p2: int,
    s1: int, s2: int,
    dice: list[tuple[int, int]],
    n: int = 1,
) -> list[int]:
    result = [0, 0]
    for roll, multiplicity in dice:
        position = (p1 + roll) % 10
        score = s1 + position + 1
        if score >= 21:
            result[n1] += multiplicity * n
        else:
            results = part_2(n2, n1, p2, position, s2, score, dice, n=n * multiplicity)
            for name, val in enumerate(results):
                result[name] += val
    return result


def main() -> None:
    print(part_1(read_input("input")))

    dice = sorted(Counter(sum(xs) for xs in product(range(1, 4), repeat=3)).items())
    p1, p2 = read_input("input")
    result = part_2(0, 1, p1.position, p2.position, 0, 0, dice)
    print(max(result))


if __name__ == "__main__":
    main()
