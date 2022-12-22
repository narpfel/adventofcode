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


def wrap_plain(maze, x, y, facing):
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


def move_plain(maze, x, y, facing):
    x, y = move(x, y, facing)
    return *wrap_plain(maze, x, y, facing), facing


def check_move(maze, x, y, facing, move):
    x, y, facing = move(maze, x, y, facing)
    if maze[x, y] == ".":
        return x, y, facing
    elif maze[x, y] == "#":
        raise Blocked


def get_face(x, y):
    if x in range(50, 100) and y in range(50):
        return 1
    elif x in range(100, 150) and y in range(50):
        return 2
    elif x in range(50, 100) and y in range(50, 100):
        return 3
    elif x in range(50) and y in range(100, 150):
        return 4
    elif x in range(50, 100) and y in range(100, 150):
        return 5
    elif x in range(50) and y in range(150, 200):
        return 6
    else:
        assert False, f"unreachable: {x, y}"


def move_cube(maze, x, y, facing):
    moved_x, moved_y = move(x, y, facing)
    if (moved_x, moved_y) in maze:
        return moved_x, moved_y, facing
    else:
        match get_face(x, y), facing:
            # paper models FTW!
            case 1, "^":
                return 0, x - 50 + 150, ">"
            case 1, "<":
                return 0, 100 + 49 - y, ">"
            case 2, "^":
                return x - 100, 199, "^"
            case 2, ">":
                return 99, 149 - y, "<"
            case 2, "v":
                return 99, x - 50, "<"
            case 5, "v":
                return 49, x - 50 + 150, "<"
            case 4, "^":
                return 50, x + 50, ">"
            case 6, "<":
                return y - 150 + 50, 0, "v"
            case 4, "<":
                return 50, 100 - y + 49, ">"
            case 6, "v":
                return x + 100, 0, "v"
            case 5, ">":
                return 149, 149 - y, "<"
            case 3, ">":
                return y + 50, 49, "^"
            case 6, ">":
                return y - 150 + 50, 149, "^"
            case 3, "<":
                return y - 50, 100, "v"
            case default:
                assert False, default


def solve(maze, directions, move):
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
                    x, y, facing = check_move(maze, x, y, facing, move)
            except Blocked:
                pass

    return 1000 * (y + 1) + 4 * (x + 1) + ">v<^".index(facing)


def test_part_1():
    maze, directions = read_input("input_test")
    assert solve(maze, directions, move_plain) == EXPECTED_PART_1


def main():
    maze, directions = read_input("input")
    print(solve(maze, directions, move_plain))
    print(solve(maze, directions, move_cube))


if __name__ == "__main__":
    main()
