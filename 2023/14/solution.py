#!/usr/bin/env pypy3

from itertools import count
from itertools import product

EXPECTED_PART_1 = 136
EXPECTED_PART_2 = 64

TOTAL_CYCLE_COUNT = 1000000000


def read_input(filename):
    with open(filename) as lines:
        round = set()
        square = set()
        for y, line in enumerate(lines):
            for x, c in enumerate(line.strip()):
                if c == "O":
                    round.add((x, y))
                elif c == "#":
                    square.add((x, y))
                else:
                    assert c == "."
    return (x, y), round, square


def part_1(puzzle_input):
    (max_x, max_y), round, square = puzzle_input
    xrange = range(max_x + 1)
    yrange = range(max_y + 1)

    for y, x in product(yrange, xrange):
        if (x, y) in round:
            round.remove((x, y))
            while True:
                y -= 1
                rock = x, y
                if rock in round or rock in square or x not in xrange or y not in yrange:
                    y += 1
                    break
            round.add((x, y))

    return sum(
        max_y + 1 - y
        for _, y in round
    )


def part_2(puzzle_input):
    (max_x, max_y), round, square = puzzle_input
    xrange = range(max_x + 1)
    yrange = range(max_y + 1)
    seen = {}

    for i in count():
        frozen_round = frozenset(round)
        if frozen_round in seen:
            break
        else:
            seen[frozen_round] = i

        for x_offset, y_offset, all_points in [
            (0, -1, product(yrange, xrange)),
            (-1, 0, product(yrange, xrange)),
            (0, 1, product(reversed(yrange), xrange)),
            (1, 0, product(yrange, reversed(xrange))),
        ]:
            for y, x in all_points:
                if (x, y) in round:
                    round.remove((x, y))
                    while True:
                        rock = x, y = x + x_offset, y + y_offset
                        if rock in round or rock in square or x not in xrange or y not in yrange:
                            x, y = x - x_offset, y - y_offset
                            break
                    round.add((x, y))

    seen_at = {
        v: k for k, v in seen.items()
    }
    cycle_start = seen[frozen_round]
    cycle_length = i - cycle_start
    rest = (TOTAL_CYCLE_COUNT - cycle_start) % cycle_length
    return sum(
        max_y + 1 - y
        for _, y in seen_at[cycle_start + rest]
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
