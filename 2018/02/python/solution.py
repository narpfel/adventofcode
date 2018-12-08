#!/usr/bin/env python3

from collections import Counter
from itertools import combinations


def part1(lines):
    letter_counts = [set(Counter(line).values()) for line in lines]
    return (
        sum(2 in c for c in letter_counts)
        * sum(3 in c for c in letter_counts)
    )


def hamming_distance(word1, word2):
    return sum(c1 != c2 for c1, c2 in zip(word1, word2))


def part2(lines):
    """TODO: This only works if the differing character occurs only once in the string."""
    for word1, word2 in combinations(lines, 2):
        if hamming_distance(word1, word2) == 1:
            difference = next(iter(set(word1).difference(word2)))
            return word1.replace(difference, "")


def main():
    with open("input") as lines:
        lines = [line.strip() for line in lines]

    print(part1(lines))
    print(part2(lines))


if __name__ == "__main__":
    main()
