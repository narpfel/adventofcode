#!/usr/bin/env pypy3

from itertools import product

EXPECTED_PART_1 = 136


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


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
