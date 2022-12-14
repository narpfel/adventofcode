#!/usr/bin/env pypy3

from itertools import tee

EXPECTED_PART_1 = 24
EXPECTED_PART_2 = 93

FULL = object()


def pairwise(xs):
    xs, ys = tee(xs)
    next(ys, None)
    return zip(xs, ys)


def place_tiles(lines):
    tiles = {}
    for line in lines:
        for ((x, y), (X, Y)) in pairwise(line):
            if x == X:
                for q in range(min(y, Y), max(y, Y) + 1):
                    tiles[x, q] = "#"
            elif y == Y:
                for q in range(min(x, X), max(x, X) + 1):
                    tiles[q, y] = "#"
            else:
                assert False

    return tiles


def parse_tuple(s):
    return tuple(map(int, s.split(",")))


def read_input(filename):
    with open(filename) as lines:
        return place_tiles(map(parse_tuple, line.split(" -> ")) for line in lines)


def drop(tiles, x, y, max_y):
    if (500, 0) in tiles:
        return FULL

    while (x, y + 1) not in tiles and y + 1 < max_y:
        y += 1

    if y == max_y:
        return FULL

    if (x - 1, y + 1) not in tiles:
        return drop(tiles, x - 1, y + 1, max_y)
    elif (x + 1, y + 1) not in tiles:
        return drop(tiles, x + 1, y + 1, max_y)

    tiles[x, y] = "o"
    return None


def drop_until_full(tiles):
    max_y = max(y for _, y in tiles)
    while drop(tiles, 500, 0, max_y) is not FULL:
        pass
    return sum(tile == "o" for tile in tiles.values())


def part_1(tiles):
    return drop_until_full(tiles)


def part_2(tiles):
    max_y = max(y for _, y in tiles) + 2
    for x in range(-1_000, 1_000):
        tiles[x, max_y] = "#"

    return drop_until_full(tiles)


def test_part_1():
    tiles = read_input("input_test")
    assert part_1(tiles) == EXPECTED_PART_1


def test_part_2():
    tiles = read_input("input_test")
    assert part_2(tiles) == EXPECTED_PART_2


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
