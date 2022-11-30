#!/usr/bin/env pypy3

import argparse
import re
from itertools import count

LINE_RE = re.compile(r"(x|y)=(\d+), .=(\d+)\.\.(\d+)")


def drop(tiles, x, y, max_y):
    while (x, y + 1) not in tiles and y < max_y:
        y += 1

    if y == max_y:
        tiles[x, y] = "|"
        return

    if tiles.get((x, y + 1)) == "|":
        tiles[x, y] = "|"
        return

    x_orig = x
    while (x - 1, y) not in tiles:
        if tiles.get((x, y + 1)) == "|":
            tiles[x, y] = "|"
            return

        x -= 1
        if (x, y + 1) not in tiles:
            drop(tiles, x, y, max_y)
            return

    if x == x_orig:
        while (x + 1, y) not in tiles:
            if tiles.get((x, y + 1)) == "|":
                tiles[x, y] = "|"
                return

            x += 1
            if (x, y + 1) not in tiles:
                drop(tiles, x, y, max_y)
                return

    if tiles.get((x + 1, y)) == "|" or tiles.get((x - 1, y)) == "|":
        tiles[x, y] = "|"
        return

    if tiles.get((x, y + 1)):
        wall_count = 0
        for direction in count(step=-1), count():
            for i in direction:
                if (x + i, y + 1) not in tiles:
                    break
                if tiles.get((x + i, y)) == "#":
                    wall_count += 1
                    break

        if wall_count == 2:
            tiles[x, y] = "~"
        else:
            while (x, y) not in tiles:
                drop(tiles, x, y, max_y)
        return

    raise AssertionError("unreachable")  # pragma: no cover (unreachable)


def show(tiles):
    min_x = min(x for x, _ in tiles)
    max_x = max(x for x, _ in tiles)
    min_y = min(y for _, y in tiles)
    max_y = max(y for _, y in tiles)
    for y in range(min(0, min_y), max_y + 1):
        for x in range(min_x, max_x + 1):
            tile = tiles.get((x, y), "+" if (x, y) == (500, 0) else " ")
            if tile in "~|":
                tile = f"\x1b[1m\x1b[31m{tile}\x1b[0m"
            print(tile, end="")
        print()


def read_input(filename):
    tiles = {}

    with open(filename) as lines:
        for line in lines:
            match = LINE_RE.fullmatch(line.strip())
            assert match is not None
            if match[1] == "x":
                x = int(match[2])
                for y in range(int(match[3]), int(match[4]) + 1):
                    tiles[(x, y)] = "#"
            else:
                y = int(match[2])
                for x in range(int(match[3]), int(match[4]) + 1):
                    tiles[(x, y)] = "#"

    return tiles


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("-v", "--visualise", action="store_true")
    args = parser.parse_args(argv)

    tiles = read_input("input")
    max_y = max(y for _, y in tiles)
    min_y = min(y for _, y in tiles)

    while (500, min_y) not in tiles:
        drop(tiles, 500, min_y - 1, max_y)

    if args.visualise:
        show(tiles)

    flowing_tiles = sum(tile == "|" for tile in tiles.values())
    resting_tiles = sum(tile == "~" for tile in tiles.values())
    print(flowing_tiles + resting_tiles)
    print(resting_tiles)


if __name__ == "__main__":
    main()
