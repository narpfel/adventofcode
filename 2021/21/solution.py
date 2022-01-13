#!/usr/bin/env python3

from itertools import cycle

from more_itertools import chunked


class Player:
    def __init__(self, position):
        self.position = position - 1
        self.score = 0

    def roll(self, roll):
        self.position = (self.position + roll) % 10
        self.score += self.position + 1


def main():
    with open("input") as lines:
        players = [Player(int(line.split()[-1])) for line in lines]

    die = cycle(range(1, 101))
    rolls = map(sum, chunked(die, 3))
    for i, (player, roll) in enumerate(zip(cycle(players), rolls), 1):
        player.roll(roll)
        if player.score >= 1000:
            break

    print(i * 3 * min(player.score for player in players))


if __name__ == "__main__":
    main()
