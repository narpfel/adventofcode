#!/usr/bin/env pypy3

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


def play_recursive_combat(players):
    seen = set()
    while True:
        if players in seen:
            return 0, None
        else:
            seen.add(players)
            cards = players[0][0], players[1][0]
            players = players[0][1:], players[1][1:]
            if (
                len(players[0]) >= cards[0]
                and len(players[1]) >= cards[1]
            ):
                result, _ = play_recursive_combat((
                    players[0][:cards[0]],
                    players[1][:cards[1]],
                ))
            else:
                result = 0 if cards[0] > cards[1] else 1

        cards = cards[result], cards[not result]
        players = (
            players[0] + (cards if result == 0 else ()),
            players[1] + (cards if result == 1 else ()),
        )
        if not all(players):
            result = 1 if not players[0] else 0
            return result, sum(
                i * n
                for i, n in enumerate(
                    reversed(players[result]),
                    start=1,
                )
            )


def test_part_1():
    assert play_combat(read_input("input_test")) == 306


def test_part_2():
    assert play_recursive_combat(
        tuple(tuple(player) for player in read_input("input_test_part_2")),
    )[0] == 0
    assert play_recursive_combat(
        tuple(tuple(player) for player in read_input("input_test")),
    ) == (1, 291)


def main():
    print(play_combat(read_input("input")))
    print(play_recursive_combat(tuple(tuple(player) for player in read_input("input")))[1])


if __name__ == "__main__":
    main()
