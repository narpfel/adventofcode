#!/usr/bin/env python3

EXPECTED_PART_1 = 6


def read_input(filename):
    with open(filename) as lines:
        patterns, towels = lines.read().split("\n\n")
        return patterns.strip().split(", "), towels.strip().splitlines()


def is_possible(patterns, towel):
    if not towel:
        return True
    else:
        return any(
            is_possible(patterns, towel.removeprefix(pattern))
            for pattern in patterns
            if towel.startswith(pattern)
        )


def part_1(puzzle_input):
    patterns, towels = puzzle_input
    return sum(is_possible(patterns, towel) for towel in towels)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
