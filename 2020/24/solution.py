#!/usr/bin/env pypy3

import re
from collections import defaultdict
from itertools import product

INSTRUCTION = re.compile("e|se|sw|w|nw|ne")


def parse_line(line):
    return INSTRUCTION.findall(line)


def parse_input(filename):
    with open(filename) as lines:
        return [parse_line(line) for line in lines]


def apply_steps(paths):
    floor = defaultdict(bool)
    for path in paths:
        x = 0
        y = 0
        for step in path:
            match step:
                case "e":
                    x += 2
                case "se":
                    x += 1
                    y += 1
                case "sw":
                    x -= 1
                    y += 1
                case "w":
                    x -= 2
                case "nw":
                    x -= 1
                    y -= 1
                case "ne":
                    x += 1
                    y -= 1
                case _:
                    assert False, step
        floor[x, y] = not floor[x, y]
    return floor


def count_black_neighbour_tiles(floor, x, y):
    return (
        floor.get((x + 2, y), False)
        + floor.get((x + 1, y + 1), False)
        + floor.get((x - 1, y + 1), False)
        + floor.get((x - 2, y), False)
        + floor.get((x - 1, y - 1), False)
        + floor.get((x + 1, y - 1), False)
    )


def flip_tiles(floor):
    new_floor = {}
    min_x = min(x for x, _ in floor)
    max_x = max(x for x, _ in floor)
    min_y = min(y for _, y in floor)
    max_y = max(y for _, y in floor)
    for x, y in product(range(min_x - 2, max_x + 3), range(min_y - 2, max_y + 3)):
        colour = floor.get((x, y), False)
        black_neighbour_tile_count = count_black_neighbour_tiles(floor, x, y)
        if colour and (black_neighbour_tile_count == 0 or black_neighbour_tile_count > 2):
            new_floor[x, y] = not colour
        elif not colour and black_neighbour_tile_count == 2:
            new_floor[x, y] = not colour
        else:
            new_floor[x, y] = colour
    return new_floor


def part_1(filename):
    paths = parse_input(filename)
    floor = apply_steps(paths)
    return sum(floor.values())


def part_2(filename):
    paths = parse_input(filename)
    floor = apply_steps(paths)
    for _ in range(100):
        floor = flip_tiles(floor)
    return sum(floor.values())


def test_part1():
    assert part_1("input_test") == 10


def test_part2():
    assert part_2("input_test") == 2208


def main():
    print(part_1("input"))
    print(part_2("input"))


if __name__ == "__main__":
    main()
