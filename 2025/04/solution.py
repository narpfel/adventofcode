#!/usr/bin/env python3

EXPECTED_PART_1 = 13


def read_input(filename):
    with open(filename) as lines:
        tiles = set()
        for y, line in enumerate(lines):
            for x, c in enumerate(line.strip()):
                if c == "@":
                    tiles.add((x, y))
        return tiles


def neighbours(x, y):
    yield x + 1, y
    yield x + 1, y + 1
    yield x + 1, y - 1
    yield x - 1, y
    yield x - 1, y + 1
    yield x - 1, y - 1
    yield x, y + 1
    yield x, y - 1


def accessible(tiles):
    for x, y in tiles:
        if sum(tile in tiles for tile in neighbours(x, y)) < 4:
            yield x, y


def part_1(tiles):
    return sum(1 for _ in accessible(tiles))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    tiles = read_input("input")
    print(part_1(tiles))


if __name__ == "__main__":
    main()
