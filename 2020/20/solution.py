#!/usr/bin/env python3

import re
import sys
from itertools import groupby
from itertools import product
from math import sqrt
from operator import attrgetter

import attr
import numpy as np

ID = re.compile(r"Tile (\d{4}):")

TRANSFORMATIONS = [
    lambda x: x,
    np.rot90,
    np.rot90,
    np.rot90,
    np.fliplr,
    np.rot90,
    np.rot90,
    np.rot90,
]

SEA_MONSTER_SHAPE = [
    "                  # ",
    "#    ##    ##    ###",
    " #  #  #  #  #  #   ",
]


def to_number(bits):
    return int("".join(str(int(bit)) for bit in bits), 2)


@attr.s(frozen=True)
class Tile:
    id = attr.ib()
    left = attr.ib()
    right = attr.ib()
    top = attr.ib()
    bottom = attr.ib()
    tile = attr.ib(eq=False)

    @classmethod
    def new(cls, id, tile):
        left = to_number(tile[:, 0])
        right = to_number(tile[:, -1])
        top = to_number(tile[0, :])
        bottom = to_number(tile[-1, :])
        assert tile.shape[0] == tile.shape[1]
        return cls(
            id=id,
            left=left,
            right=right,
            top=top,
            bottom=bottom,
            tile=tile,
        )


def all_orientations(tile):
    for transform in TRANSFORMATIONS:
        tile = transform(tile)
        yield tile


def read_name(name):
    return int(ID.search(name).group(1))


def to_array(tile):
    return np.array([[x == "#" for x in xs] for xs in tile])


def parse_tile(s):
    name, *tile = s.splitlines()
    return read_name(name), to_array(tile)


def by_border(tiles, border_name):
    return {
        border: frozenset(tiles)
        for border, tiles in groupby(
            sorted(tiles, key=attrgetter(border_name)),
            key=attrgetter(border_name),
        )
    }


def solve(tiles):
    def go(used_tiles, grid, i, j, tile):
        assert grid[i][j] is None

        if not (
            (i == 0 or tile.top == grid[i - 1][j].bottom)
            and (j == 0 or tile.left == grid[i][j - 1].right)
        ):
            return False

        if i == j == puzzle_size - 1:
            grid[i][j] = tile
            return True

        if j == puzzle_size - 1:
            possible_tiles = tops.get(grid[i][0].bottom, frozenset())
            next_i = i + 1
            next_j = 0
        else:
            possible_tiles = lefts.get(tile.right, frozenset())
            if i > 0 and j < puzzle_size - 1:
                possible_tiles &= tops.get(grid[i - 1][j + 1].bottom, frozenset())
            next_i = i
            next_j = j + 1

        if possible_tiles:
            grid[i][j] = tile
            used_tiles.add(tile.id)

        return any(
            go(used_tiles, grid, next_i, next_j, next_tile)
            for next_tile in possible_tiles
            if next_tile.id not in used_tiles
        )

    puzzle_size = int(sqrt(len(tiles) // 8))
    lefts = by_border(tiles, "left")
    tops = by_border(tiles, "top")

    for tile in tiles:
        grid = [[None] * puzzle_size for _ in range(puzzle_size)]
        if go(set(), grid, 0, 0, tile):
            return grid

    raise ValueError("unsolvable")


def main():
    with open("input") as file:
        tiles = dict(parse_tile(s) for s in file.read().strip().split("\n\n"))

    all_tiles = [
        Tile.new(id, orientation)
        for id, tile in tiles.items()
        for orientation in all_orientations(tile)
    ]

    solution = solve(all_tiles)
    if len(sys.argv) >= 2 and "--visualise" == sys.argv[1]:
        print("\n".join(" ".join(str(tile.id) for tile in line) for line in solution))
    print(solution[0][0].id * solution[0][-1].id * solution[-1][0].id * solution[-1][-1].id)

    image = np.block([[tile.tile[1:-1, 1:-1] for tile in row] for row in solution])

    sea_monster = to_array(SEA_MONSTER_SHAPE)
    y, x = sea_monster.shape
    for transform in TRANSFORMATIONS:
        image = transform(image)
        for i, j in product(range(len(image)), repeat=2):
            sub = image[i:i + y, j:j + x]
            if sub.shape == sea_monster.shape and ((sub & sea_monster) == sea_monster).all():
                sub &= ~sea_monster
    print(image.sum())


if __name__ == "__main__":
    main()
