#!/usr/bin/env python3

from collections import Counter

EXPECTED_PART_1 = 21
EXPECTED_PART_2 = 40


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def solve(manifold):
    beam_positions = Counter([manifold[0].index("S")])
    splits = 0
    for line in manifold[1:]:
        new_beam_positions = Counter()
        for x in beam_positions:
            if line[x] == "^":
                new_beam_positions[x - 1] += beam_positions[x]
                new_beam_positions[x + 1] += beam_positions[x]
                splits += 1
            else:
                new_beam_positions[x] += beam_positions[x]
        beam_positions = new_beam_positions
    return splits, beam_positions.total()


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[0] == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[1] == EXPECTED_PART_2


def main():
    manifold = read_input("input")
    part_1, part_2 = solve(manifold)
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
