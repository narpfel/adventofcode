#!/usr/bin/env python3

from itertools import pairwise

EXPECTED_PART_1 = 114


def read_input(filename):
    with open(filename) as lines:
        return [
            [int(n) for n in line.split()]
            for line in lines
        ]


def extrapolate(xss):
    for xs in xss:
        difference_stack = [xs]
        differences = xs

        while True:
            differences = [b - a for a, b in zip(differences, differences[1:])]
            difference_stack.append(differences)
            if set(differences) == {0}:
                break

        for d1, d2 in pairwise(reversed(difference_stack)):
            d2.append(d2[-1] + d1[-1])


def part_1(xss):
    return sum(xs[-1] for xs in xss)


def test_part_1():
    puzzle_input = read_input("input_test")
    extrapolate(puzzle_input)
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    xss = read_input("input")
    extrapolate(xss)
    print(part_1(xss))


if __name__ == "__main__":
    main()
