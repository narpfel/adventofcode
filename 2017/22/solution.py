#!/usr/bin/env python3
from collections import defaultdict

STEP_COUNT = 10_000


def left(position):
    x, y = position
    return x - 1, y


def right(position):
    x, y = position
    return x + 1, y


def up(position):
    x, y = position
    return x, y - 1


def down(position):
    x, y = position
    return x, y + 1


MOVE = [left, up, right, down]


def next_direction(cell, direction):
    return (direction + (1 if cell else -1)) % len(MOVE)


def step(grid, position, direction):
    direction = next_direction(grid[position], direction)
    grid[position] ^= True
    has_caused_infection = grid[position]
    position = MOVE[direction](position)
    return position, direction, has_caused_infection


def read_input(input_filename):
    grid = defaultdict(bool)
    with open(input_filename) as lines:
        for y, line in enumerate(lines):
            for x, node in enumerate(line.strip()):
                grid[(x, y)] = node == "#"
    return grid


def solve(input_filename):
    grid = read_input(input_filename)
    direction = MOVE.index(up)
    size_x = max(x for x, _ in grid)
    size_y = max(y for _, y in grid)
    if size_x % 2 != 0 or size_y % 2 != 0:
        raise ValueError("input must have odd size in both dimentions")
    position = (size_x + 1) // 2, (size_y + 1) // 2

    infections_caused = 0
    for _ in range(STEP_COUNT):
        position, direction, has_caused_infection = step(grid, position, direction)
        infections_caused += has_caused_infection

    return infections_caused


def test_part1_with_test_input():
    assert solve("input_test") == 5587


def main():
    print(solve("input"))


if __name__ == "__main__":
    main()
