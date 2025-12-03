#!/usr/bin/env python3

EXPECTED_PART_1 = 357
EXPECTED_PART_2 = 3121910778619


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(banks):
    return sum(
        max(
            int(first + second)
            for i, first in enumerate(bank)
            for second in bank[i + 1:]
        )
        for bank in banks
    )


def select_ith(bank, indices, i):
    indices = indices + [i]
    indices.sort()
    return "".join(bank[i] for i in indices), indices


def select_best(bank, n):
    selected = ""
    indices = []
    for _ in range(n):
        selected, indices = max(
            select_ith(bank, indices, i)
            for i in range(len(bank))
            if i not in indices
        )
    return int(selected)


def part_2(banks):
    return sum(select_best(bank, 12) for bank in banks)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    banks = read_input("input")
    print(part_1(banks))
    print(part_2(banks))


if __name__ == "__main__":
    main()
