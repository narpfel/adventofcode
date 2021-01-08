#!/usr/bin/env pypy3
import re
from collections import deque
from itertools import cycle

INPUT = "493 players; last marble is worth 71863 points"


def play(player_count, highest_marble_number):
    scores = [0] * player_count
    marbles = deque([0])
    for marble, player in zip(range(1, highest_marble_number + 1), cycle(range(player_count))):
        if marble % 23:
            marbles.rotate(2)
            marbles.append(marble)
        else:
            marbles.rotate(-7)
            scores[player] += marble + marbles.pop()
    return max(scores)


def main():
    player_count, highest_marble_number = map(
        int,
        re.match(r"(\d+) players; last marble is worth (\d+) points", INPUT).groups(),
    )
    print(play(player_count, highest_marble_number))
    print(play(player_count, highest_marble_number * 100))


if __name__ == "__main__":
    main()
