#!/usr/bin/env pypy3

from itertools import cycle

EXPECTED_PART_1 = 41

UP = (0, -1)
RIGHT = (1, 0)
DOWN = (0, 1)
LEFT = (-1, 0)


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def parse_input(puzzle_input):
    tiles = {}
    for y, line in enumerate(puzzle_input):
        for x, c in enumerate(line):
            tiles[x, y] = c
    x, y = next((x, y) for ((x, y), c) in tiles.items() if c == "^")
    return tiles, x, y


class HasLoop(BaseException):
    pass


def move(x, y, direction):
    dx, dy = direction
    return x + dx, y + dy


def find_path(tiles, x, y):
    directions = cycle([UP, RIGHT, DOWN, LEFT])
    direction = next(directions)
    visited = set()
    while True:
        if (x, y, direction) in visited:
            raise HasLoop
        visited.add((x, y, direction))

        nx, ny = move(x, y, direction)
        if (nx, ny) not in tiles:
            return visited

        while tiles[nx, ny] == "#":
            direction = next(directions)
            nx, ny = move(x, y, direction)

        x, y = nx, ny


def part_1(puzzle_input):
    tiles, x, y = parse_input(puzzle_input)
    return len({(x, y) for (x, y, _) in find_path(tiles, x, y)})


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
