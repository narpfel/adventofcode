#!/usr/bin/env python3

EXPECTED_PART_1 = 21


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(manifold):
    beam_positions = {manifold[0].index("S")}
    splits = 0
    for line in manifold[1:]:
        new_beam_positions = set()
        for x in beam_positions:
            if line[x] == "^":
                new_beam_positions.add(x - 1)
                new_beam_positions.add(x + 1)
                splits += 1
            else:
                new_beam_positions.add(x)
        beam_positions = new_beam_positions
    return splits


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    manifold = read_input("input")
    print(part_1(manifold))


if __name__ == "__main__":
    main()
