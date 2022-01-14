#!/usr/bin/env pypy3

from collections import Counter
from itertools import cycle
from itertools import product


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


# removing all abstractions improves performance by ~15x on PyPy
def part_2(n1, n2, p1, p2, s1, s2, dice, n=1):
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


def main():
    print(part_1(read_input("input")))

    dice = sorted(Counter(map(sum, product(range(1, 4), repeat=3))).items())
    p1, p2 = read_input("input")
    result = part_2(0, 1, p1.position, p2.position, 0, 0, dice)
    print(max(result))


if __name__ == "__main__":
    main()
