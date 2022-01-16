#!/usr/bin/env pypy3

from collections import Counter
from functools import lru_cache
from itertools import cycle
from itertools import product

DICE = sorted(Counter(map(sum, product(range(1, 4), repeat=3))).items())


class Player:
    def __init__(self, position, name):
        self.name = name
        self.position = position - 1
        self.score = 0

    def roll(self, roll):
        self.position = (self.position + roll) % 10
        self.score += self.position + 1


def read_input(filename):
    with open(filename) as lines:
        return [Player(int(line.split()[-1]), i) for i, line in enumerate(lines)]


def chunked(xs, n):
    xs = iter(xs)
    return zip(*[xs] * n)


def part_1(players):
    die = cycle(range(1, 101))
    rolls = map(sum, chunked(die, 3))
    for i, (player, roll) in enumerate(zip(cycle(players), rolls), 1):
        player.roll(roll)
        if player.score >= 1000:
            break

    return i * 3 * min(player.score for player in players)


@lru_cache(maxsize=None)
def part_2(p1, p2, s1, s2):
    wins1, wins2 = 0, 0
    for roll, multiplicity in DICE:
        position = (p1 + roll) % 10
        score = s1 + position + 1
        if score >= 21:
            wins1 += multiplicity
        else:
            w2, w1 = part_2(p2, position, s2, score)
            wins1 += w1 * multiplicity
            wins2 += w2 * multiplicity
    return wins1, wins2


def main():
    print(part_1(read_input("input")))

    p1, p2 = read_input("input")
    # clear cache to not influence benchmarking
    part_2.cache_clear()
    result = part_2(p1.position, p2.position, 0, 0)
    print(max(result))


if __name__ == "__main__":
    main()
