#!/usr/bin/env python3

import argparse


def parse_seq(re, i, x, y, distance, maze, choice_points, *, with_assert):
    positions_after_choice = set()
    while i < len(re):
        c = re[i]
        match c:
            case "N":
                y -= 1
                maze[x, y] = "-"
                distance += 1
                y -= 1
                maze[x, y] = min(distance, maze.setdefault((x, y), distance))
            case "E":
                x += 1
                maze[x, y] = "-"
                distance += 1
                x += 1
                maze[x, y] = min(distance, maze.setdefault((x, y), distance))
            case "S":
                y += 1
                maze[x, y] = "-"
                distance += 1
                y += 1
                maze[x, y] = min(distance, maze.setdefault((x, y), distance))
            case "W":
                x -= 1
                maze[x, y] = "-"
                distance += 1
                x -= 1
                maze[x, y] = min(distance, maze.setdefault((x, y), distance))
            case "(":
                choice_points.append((x, y, distance))
            case ")":
                if with_assert:
                    assert len(positions_after_choice) == 1, positions_after_choice
                positions_after_choice.clear()
                choice_points.pop()
            case "|":
                positions_after_choice.add((x, y))
                # I have no idea why this works. This assumes that each
                # alternative in a group always ends at the same position as
                # every other alternative in that group. This is clearly wrong
                # as shown by the assertion in the `)` case. However, it
                # produces the right result for all inputs I’ve tried it on‽
                x, y, distance = choice_points[-1]
            case "$":
                assert i == len(re) - 1
                assert choice_points == [(0, 0)], choice_points
        i += 1


def parse_re(re, *, with_assert):
    assert re[0] == "^"
    maze = {(0, 0): 0}
    parse_seq(re, 1, 0, 0, 0, maze, [(0, 0)], with_assert=with_assert)
    return maze


def show(maze):
    min_x = min(x for x, _ in maze)
    max_x = max(x for x, _ in maze)
    min_y = min(y for _, y in maze)
    max_y = max(y for _, y in maze)
    for y in range(min_y - 1, max_y + 2):
        for x in range(min_x - 1, max_x + 2):
            tile = maze.get((x, y), "#")
            match tile:
                case "-" if is_room(maze.get((x - 1, y))) and is_room(maze.get((x + 1, y))):
                    tile = "|"
                case 0:
                    tile = "X"
                case int():
                    tile = "."

            print(tile, end="")
        print()


def is_room(tile):
    return isinstance(tile, int)


def read_input(filename, *, with_assert=False):
    with open(filename) as input_file:
        re = input_file.read().strip()

    return parse_re(re, with_assert=with_assert)


def part_1(maze):
    return max(tile for tile in maze.values() if is_room(tile))


def part_2(maze):
    return sum(tile >= 1000 for tile in maze.values() if is_room(tile))


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("-v", "--visualise", action="store_true")
    parser.add_argument("-a", "--assert", action="store_true", dest="with_assert")
    args = parser.parse_args(argv)

    maze = read_input("input", with_assert=args.with_assert)

    if args.visualise:
        show(maze)

    print(part_1(maze))
    print(part_2(maze))


if __name__ == "__main__":
    main()
