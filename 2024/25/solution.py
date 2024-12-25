#!/usr/bin/env python3

from itertools import combinations

EXPECTED_PART_1 = 3


def transpose(xss):
    return zip(*xss)


def read_input(filename):
    with open(filename) as lines:
        return [
            (key[0] == ".", [column.count("#") for column in transpose(key.splitlines())])
            for key in lines.read().split("\n\n")
        ]


def part_1(keys):
    return sum(
        lhs_kind != rhs_kind and all(x + y <= 7 for x, y in zip(lhs_key, rhs_key))
        for (lhs_kind, lhs_key), (rhs_kind, rhs_key) in combinations(keys, r=2)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
