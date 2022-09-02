#!/usr/bin/env python3

from collections import deque
from itertools import chain


def read_input(filename):
    with open(filename) as file:
        players = file.read().split("\n\n")

    return [
        deque(int(card) for card in player.splitlines()[1:])
        for player in players
    ]


def play_combat(players):
    while True:
        cards = [player.popleft() for player in players]
        players[0 if cards[0] > cards[1] else 1].extend(sorted(cards, reverse=True))
        if not all(players):
            return sum(
                i * n
                for i, n in enumerate(
                    reversed(list(chain.from_iterable(players))),
                    start=1,
                )
            )


def test_part_1():
    assert play_combat(read_input("input_test")) == 306


def main():
    print(play_combat(read_input("input")))


if __name__ == "__main__":
    main()
