#!/usr/bin/env python3

from functools import cache
from itertools import cycle

SHAPES_STRING = """
####

.#.
###
.#.

..#
..#
###

#
#
#
#

##
##
""".strip()

SHAPES = [shape.splitlines() for shape in SHAPES_STRING.split("\n\n")]
MAX_SHAPE_HEIGHT = max(len(shape) for shape in SHAPES)

PART_1_ROCK_COUNT = 2022
PART_2_ROCK_COUNT = 1_000_000_000_000

EXPECTED_PART_1 = 3068
EXPECTED_PART_2 = 1514285714288


def read_input(filename):
    with open(filename) as lines:
        return next(lines).strip()


@cache
def find_periodicity(directions):
    cave = {(x, 0) for x in range(7)}
    height = max(y for _, y in cave)
    directions = cycle(enumerate(directions))
    seen = {}
    heights = []

    for i, (shape_idx, shape) in enumerate(cycle(enumerate(SHAPES))):
        x_offset = 2
        y_offset = height + 3 + len(shape)
        shape = {
            (x_offset + x, y_offset - y)
            for y, line in enumerate(shape)
            for x, c in enumerate(line) if c == "#"
        }

        for j, direction in directions:
            if direction == "<":
                moved_shape = {(x - 1, y) for x, y in shape}
            elif direction == ">":
                moved_shape = {(x + 1, y) for x, y in shape}
            else:
                assert False, direction

            if (
                cave.isdisjoint(moved_shape)
                and all(x in range(7) for x, _ in moved_shape)
            ):
                shape = moved_shape

            moved_shape = {(x, y - 1) for x, y in shape}
            if cave.isdisjoint(moved_shape):
                shape = moved_shape
            else:
                break

        cave |= shape
        max_heights = [0] * 7
        for x, y in cave:
            max_heights[x] = max(max_heights[x], y)
        min_height = min(max_heights)
        cave = {(x, y) for x, y in cave if y >= min_height - MAX_SHAPE_HEIGHT}
        height = max(max(y for _, y in shape), height)
        heights.append(height)

        state = shape_idx, j, frozenset((x, y - height) for x, y in cave)
        if state in seen:
            return (seen[state], i), heights

        seen[state] = i


def tower_height(directions, rock_count):
    (begin, end), heights = find_periodicity(directions)
    iterations_in_cycle = rock_count - begin
    loop_length = end - begin
    loop_count, rest = divmod(iterations_in_cycle, loop_length)
    return loop_count * (heights[end] - heights[begin]) + heights[begin + rest - 1]


def test_part_1():
    assert tower_height(read_input("input_test"), 2022) == EXPECTED_PART_1


def test_part_2():
    assert tower_height(read_input("input"), 20220) == 30894
    assert tower_height(read_input("input_test"), PART_2_ROCK_COUNT) == EXPECTED_PART_2


def main():
    directions = read_input("input")
    print(tower_height(directions, PART_1_ROCK_COUNT))
    print(tower_height(directions, PART_2_ROCK_COUNT))


if __name__ == "__main__":
    main()
