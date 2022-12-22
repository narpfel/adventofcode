#!/usr/bin/env python3

import re
from itertools import count

EXPECTED_PART_1 = 6032
EXPECTED_PART_2 = 5031

RIGHT_LEFT_RE = re.compile("(R|L)")
RIGHT = {
    ">": "v",
    "v": "<",
    "<": "^",
    "^": ">",
}
LEFT = {
    ">": "^",
    "^": "<",
    "<": "v",
    "v": ">",
}


class Blocked(Exception):
    pass


def parse_maze(s):
    lines = s.splitlines()
    maze = {}
    for y, line in enumerate(lines):
        for x, c in enumerate(line):
            if c in "#.":
                maze[x, y] = c
    return maze


def read_input(filename):
    with open(filename) as file:
        maze, directions = file.read().split("\n\n")
        return parse_maze(maze), RIGHT_LEFT_RE.split(directions)


def move(x, y, facing):
    match facing:
        case ">":
            return x + 1, y
        case "v":
            return x, y + 1
        case "<":
            return x - 1, y
        case "^":
            return x, y - 1


def wrap(maze, x, y, facing):
    if (x, y) in maze:
        return x, y
    else:
        match facing:
            case ">":
                return min(x for x, y2 in maze if y == y2), y
            case "v":
                return x, min(y for x2, y in maze if x == x2)
            case "<":
                return max(x for x, y2 in maze if y == y2), y
            case "^":
                return x, max(y for x2, y in maze if x == x2)


def check_move(maze, x, y, facing):
    x, y = move(x, y, facing)
    x, y = wrap(maze, x, y, facing)
    if maze[x, y] == ".":
        return x, y
    elif maze[x, y] == "#":
        raise Blocked


def part_1(maze, directions):
    facing = ">"
    y = 0
    for x in count():
        if maze.get((x, y)) == ".":
            break

    for direction in directions:
        if direction == "R":
            facing = RIGHT[facing]
        elif direction == "L":
            facing = LEFT[facing]
        else:
            try:
                for _ in range(int(direction)):
                    x, y = check_move(maze, x, y, facing)
            except Blocked:
                pass

    return 1000 * (y + 1) + 4 * (x + 1) + ">v<^".index(facing)


def test_part_1():
    maze, directions = read_input("input_test")
    assert part_1(maze, directions) == EXPECTED_PART_1


def main():
    maze, directions = read_input("input")
    print(part_1(maze, directions))


if __name__ == "__main__":
    main()
