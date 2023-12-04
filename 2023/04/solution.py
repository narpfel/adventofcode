#!/usr/bin/env python3

EXPECTED_PART_1 = 13
EXPECTED_PART_2 = 30


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            numbers_i_have, winning_numbers = line.split(": ")[-1].split("|")
            yield (
                frozenset(map(int, numbers_i_have.split())),
                frozenset(map(int, winning_numbers.split())),
            )


def part_1(cards):
    return sum(
        2 ** (len(numbers_i_have & winning_numbers) - 1)
        for numbers_i_have, winning_numbers in cards
        if numbers_i_have & winning_numbers
    )


def part_2(cards):
    cards = list(cards)
    card_amounts = [1] * len(cards)
    for i, (numbers_i_have, winning_numbers) in enumerate(cards):
        winning_numbers_i_have = numbers_i_have & winning_numbers
        for j in range(i + 1, i + len(winning_numbers_i_have) + 1):
            card_amounts[j] += card_amounts[i]

    return sum(card_amounts)


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
