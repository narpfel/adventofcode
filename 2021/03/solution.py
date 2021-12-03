#!/usr/bin/env python3

from collections import Counter
from pathlib import Path


def part1(numbers):
    γ = 0
    ε = 0
    for column in zip(*numbers):
        (digit_γ, _), (digit_ε, _) = Counter(column).most_common(2)
        γ = 2 * γ + int(digit_γ)
        ε = 2 * ε + int(digit_ε)
    return γ * ε


def filter_for(numbers, idx, digit_for_tie):
    numbers = set(numbers)
    for i in range(len(next(iter(numbers)))):
        most_common = Counter(list(zip(*numbers))[i]).most_common(2)
        if len(most_common) > 1 and most_common[0][1] == most_common[1][1]:
            digit = digit_for_tie
        else:
            digit = most_common[idx][0]
        numbers -= {number for number in numbers if number[i] != digit}
    assert len(numbers) == 1
    return int(next(iter(numbers)), 2)


def part2(numbers):
    return filter_for(numbers, 0, "1") * filter_for(numbers, -1, "0")


def main():
    numbers = Path("input").read_text().splitlines()
    print(part1(numbers))
    print(part2(numbers))


if __name__ == "__main__":
    main()
