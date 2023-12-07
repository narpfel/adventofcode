#!/usr/bin/env python3

from collections import Counter
from functools import partial

EXPECTED_PART_1 = 6440
EXPECTED_PART_2 = 5905


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            hand, bid = line.split()
            yield hand, hand, int(bid)


CARDS = list(reversed("AKQJT98765432"))
CARDS_WITH_JOKER = list(reversed("AKQT98765432J"))


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


def hand_with_jokers_key(hand_with_bid, *, cards):
    hand, _, bid = hand_with_bid
    cards_in_hand = set(hand)
    return max(
        hand_key(
            (hand[:i] + hand[i:].replace("J", card, joker_replacement_count), hand, bid),
            cards=cards,
        )
        for joker_replacement_count in range(hand.count("J") + 1)
        for card in cards_in_hand
        for i in range(len(hand))
    )


def solve(cards, hands, key):
    key = partial(key, cards=cards)
    return sum(
        i * bid
        for i, (_, _, bid) in enumerate(sorted(hands, key=key), 1)
    )


def part_1(hands):
    return solve(CARDS, hands, hand_key)


def part_2(hands):
    return solve(CARDS_WITH_JOKER, hands, hand_with_jokers_key)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
