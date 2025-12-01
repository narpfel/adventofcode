#!/usr/bin/env python3

EXPECTED_PART_1 = 3
EXPECTED_PART_2 = 6


def read_input(filename):
    with open(filename) as lines:
        return [int(line[1:]) * (-1 if line[0] == "L" else 1) for line in lines]


def part_1(rotations):
    position = 50
    stopped_at_zero = 0
    for rotation in rotations:
        position += rotation
        position %= 100
        stopped_at_zero += position == 0
    return stopped_at_zero


def part_2(rotations):
    position = 50
    was_zero_count = 0
    for rotation in rotations:
        old_position = position
        zero_crossings, position = divmod(position + rotation, 100)
        was_zero_count += abs(zero_crossings)
        if old_position != 0 and position == 0 and rotation < 0:
            # e. g. 50 -> L50 -> 0; the `divmod` doesn’t count this
            was_zero_count += 1
        elif old_position == 0 and rotation < 0:
            # e. g. 0 -> L1 -> 99; the 0 was counted during the last rotation
            was_zero_count -= 1
    return was_zero_count


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    rotations = read_input("input")
    print(part_1(rotations))
    print(part_2(rotations))


if __name__ == "__main__":
    main()
