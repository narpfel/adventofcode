#!/usr/bin/env pypy3

from collections import UserList
from itertools import cycle


INPUT = "493 players; last marble is worth 71863 points"


def play(player_count, highest_marble_number):
    scores = [0] * player_count
    marbles = [0]
    current_marble_index = 0
    for marble, player in zip(range(1, highest_marble_number + 1), cycle(range(player_count))):
        if marble % 23:
            if current_marble_index == len(marbles) - 1:
                marbles.insert(1, marble)
                current_marble_index = 1
            else:
                marbles.insert(current_marble_index + 2, marble)
                if current_marble_index + 2 > len(marbles):
                    raise Exception(1)
                current_marble_index = (current_marble_index + 2) % len(marbles)
        else:
            current_marble_index = (current_marble_index - 7) % len(marbles)
            scores[player] += marble + marbles.pop(current_marble_index)
    return max(scores)


def main():
    print(play(493, 71863))
    # FIXME: *Way* too slow due to linear time complexity.
    # print(play(493, 71863 * 100))


if __name__ == "__main__":
    main()
