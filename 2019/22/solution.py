#!/usr/bin/env python3

PART_1_CARD_COUNT = 10_007


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


def main():
    with open("input") as lines:
        shuffle_instructions = list(lines)

    print(part_1(shuffle_instructions))


if __name__ == "__main__":
    main()
