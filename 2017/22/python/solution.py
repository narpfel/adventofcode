#!/usr/bin/env pypy3
from collections import defaultdict
from enum import IntEnum

STEP_COUNT_PART1 = 10_000
STEP_COUNT_PART2 = 10_000_000


Node = IntEnum("Node", "Clean, Weakened, Infected, Flagged")


NEXT_DIRECTION_INDEX = {
    Node.Infected: 1,
    Node.Clean: -1,
    Node.Weakened: 0,
    Node.Flagged: 2,
}

NODE_TRANSITION_PART1 = {
    Node.Infected: Node.Clean,
    Node.Clean: Node.Infected,
}

NODE_TRANSITION_PART2 = {
    Node.Clean: Node.Weakened,
    Node.Weakened: Node.Infected,
    Node.Infected: Node.Flagged,
    Node.Flagged: Node.Clean,
}


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
    return (direction + NEXT_DIRECTION_INDEX[cell]) % len(MOVE)


def step(grid, position, direction, node_transition):
    direction = next_direction(grid[position], direction)
    grid[position] = node_transition[grid[position]]
    has_caused_infection = grid[position] == Node.Infected
    position = MOVE[direction](position)
    return position, direction, has_caused_infection


def read_input(input_filename):
    grid = defaultdict(lambda: Node.Clean)
    with open(input_filename) as lines:
        for y, line in enumerate(lines):
            for x, node in enumerate(line.strip()):
                grid[(x, y)] = Node.Infected if node == "#" else Node.Clean
    return grid


def solve(input_filename, step_count, work):
    grid = read_input(input_filename)
    direction = MOVE.index(up)
    size_x = max(x for x, _ in grid)
    size_y = max(y for _, y in grid)
    if size_x % 2 != 0 or size_y % 2 != 0:
        raise ValueError("input must have odd size in both dimentions")
    position = (size_x + 1) // 2, (size_y + 1) // 2

    infections_caused = 0
    for _ in range(step_count):
        position, direction, has_caused_infection = step(grid, position, direction, work)
        infections_caused += has_caused_infection

    return infections_caused


def test_part1_with_test_input():
    assert solve("input_test", STEP_COUNT_PART1, NODE_TRANSITION_PART1) == 5587


def test_part2_with_test_input():
    assert solve("input_test", 100, NODE_TRANSITION_PART2) == 26
    assert solve("input_test", STEP_COUNT_PART2, NODE_TRANSITION_PART2) == 2511944


def main():
    print(solve("input", STEP_COUNT_PART1, NODE_TRANSITION_PART1))
    print(solve("input", STEP_COUNT_PART2, NODE_TRANSITION_PART2))


if __name__ == "__main__":
    main()
