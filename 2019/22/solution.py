#!/usr/bin/env python3

import sympy

PART_1_CARD_COUNT = 10_007

PART_2_CARD_COUNT = 119315717514047
PART_2_REPEAT_COUNT = 101741582076661


def part_1(shuffle_instructions):
    cards = list(range(PART_1_CARD_COUNT))

    for instruction in shuffle_instructions:
        if instruction == "deal into new stack\n":
            cards.reverse()
        elif instruction.startswith("deal with increment "):
            increment = int(instruction.split()[-1])
            new_cards = [None] * PART_1_CARD_COUNT
            cards.reverse()
            i = 0
            while cards:
                new_cards[i] = cards.pop()
                i += increment
                i %= PART_1_CARD_COUNT
            assert None not in new_cards
            cards = new_cards
        elif instruction.startswith("cut "):
            cut = int(instruction.split()[-1])
            cards = cards[cut:] + cards[:cut]
        else:
            assert False

    return cards.index(2019)


def geometric_sum(r, n):
    return (1 - r**n) / (1 - r)


def part_2(shuffle_instructions, *, card_count, repeat):
    x = sympy.symbols("x")
    ring = sympy.GF(card_count)
    ring_polynomial = ring[x]

    target_position = ring_polynomial(x)
    for instruction in reversed(shuffle_instructions):
        if instruction == "deal into new stack\n":
            target_position *= -1
            target_position -= 1
        elif instruction.startswith("deal with increment "):
            increment = int(instruction.split()[-1])
            target_position /= increment
        elif instruction.startswith("cut "):
            cut = int(instruction.split()[-1])
            target_position += cut
        else:
            assert False

    a, b = target_position.coeffs()

    return int((a ** repeat * 2020 + b * geometric_sum(a, repeat)).val)


def main():
    with open("input") as lines:
        shuffle_instructions = list(lines)

    print(part_1(shuffle_instructions))
    print(part_2(shuffle_instructions, card_count=PART_2_CARD_COUNT, repeat=PART_2_REPEAT_COUNT))


if __name__ == "__main__":
    main()
