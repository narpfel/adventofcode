#!/usr/bin/env python3

from collections import Counter
from functools import partial

EXPECTED_PART_1 = 6440


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            hand, bid = line.split()
            yield hand, hand, int(bid)


CARDS = list(reversed("AKQJT98765432"))


def hand_key(hand_with_bid, *, cards):
    hand, original_hand, _ = hand_with_bid
    card_counts = list(Counter(hand).values())

    has_types = [
        5 in card_counts,
        4 in card_counts,
        3 in card_counts and 2 in card_counts,
        3 in card_counts,
        card_counts.count(2) == 2,
        2 in card_counts,
        True,
    ]

    for i, has_type in enumerate(has_types):
        if has_type:
            return -i, [cards.index(c) for c in original_hand]


def solve(cards, hands, key):
    key = partial(key, cards=cards)
    return sum(
        i * bid
        for i, (_, _, bid) in enumerate(sorted(hands, key=key), 1)
    )


def part_1(hands):
    return solve(CARDS, hands, hand_key)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
