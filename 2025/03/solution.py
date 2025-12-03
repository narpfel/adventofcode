#!/usr/bin/env python3

EXPECTED_PART_1 = 357


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


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    banks = read_input("input")
    print(part_1(banks))


if __name__ == "__main__":
    main()
