#!/usr/bin/env pypy3
import sys
from itertools import chain
from itertools import count

# isort: split

sys.path.insert(0, "../10")
from solution import knot_hash  # noqa: E402 (import from modified `sys.path`)

INPUT = "jzgqcdpd"


def knot_hash_for_index(i):
    return format(int(knot_hash(f"{INPUT}-{i}".encode()), 16), "0128b")


def adjacent_to(x, y):
    return [
        (x - 1, y),
        (x + 1, y),
        (x, y - 1),
        (x, y + 1),
    ]


def in_grid(grid, x, y):
    return y in range(len(grid)) and x in range(len(grid[0]))


def fill_neighbours(grid, x, y, region_id):
    for u, v in adjacent_to(x, y):
        if in_grid(grid, u, v) and grid[v][u] is True:
            grid[v][u] = region_id
            fill_neighbours(grid, u, v, region_id)


def floodfill_regions(grid):
    region_ids = count(2)

    for y, _ in enumerate(grid):
        for x, _ in enumerate(grid[y]):
            if grid[y][x] is True:
                region_id = next(region_ids)
                grid[y][x] = region_id
                fill_neighbours(grid, x, y, region_id)


def main():
    hashes = [
        [bool(int(cell)) for cell in knot_hash_for_index(i)]
        for i in range(128)
    ]

    print(sum(sum(hash) for hash in hashes))

    floodfill_regions(hashes)
    print(len(set(chain.from_iterable(map(set, hashes))) - {False}))


if __name__ == "__main__":
    main()
