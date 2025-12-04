#!/usr/bin/env python3

EXPECTED_PART_1 = 13
EXPECTED_PART_2 = 43


def read_input(filename):
    with open(filename) as lines:
        return {
            (x, y)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
            if c == "@"
        }


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


def part_2(tiles):
    removed_tiles_count = 0
    while True:
        removable = list(accessible(tiles))
        if not removable:
            return removed_tiles_count
        removed_tiles_count += len(removable)
        tiles.difference_update(removable)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    tiles = read_input("input")
    print(part_1(tiles))
    print(part_2(tiles))


if __name__ == "__main__":
    main()
