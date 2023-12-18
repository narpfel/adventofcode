#!/usr/bin/env python3

import math
from itertools import cycle
from itertools import islice
from itertools import pairwise

EXPECTED_PART_1 = 62
EXPECTED_PART_2 = 952408144115


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            direction, distance, colour = line.split()
            yield int(distance), direction, colour.strip("#()")


def move(point, *, distance, direction):
    x, y = point
    match direction:
        case "R" | 0:
            x += distance
        case "D" | 1:
            y += distance
        case "L" | 2:
            x -= distance
        case "U" | 3:
            y -= distance
        case _:
            assert False, "unreachable"
    return x, y


def part_1(instructions):
    return part_2([(distance, direction) for distance, direction, _ in instructions])


def parse_hex_instructions(instructions):
    return [
        (int(hexdigits[:5], 16), int(hexdigits[-1], 16))
        for _, _, hexdigits in instructions
    ]


def part_2(instructions):
    point = 0, 0
    points = [point]
    for distance, direction in instructions:
        point = move(point, distance=distance, direction=direction)
        points.append(point)

    area = sum(
        (y1 + y2) * (x1 - x2)
        for (x1, y1), (x2, y2) in pairwise(points)
    )
    corners = len(instructions)
    edges = sum(distance for distance, _ in instructions)

    concave_corners = 0
    corner_points = zip(points, islice(cycle(points), 1, None), islice(cycle(points), 2, None))
    for (x1, y1), (x2, y2), (x3, y3) in corner_points:
        θ = round(
            math.degrees(
                math.atan2(y3 - y2, x3 - x2)
                - math.atan2(y1 - y2, x1 - x2),
            ),
        )
        concave_corners += (θ % 360) == 90

    # There might be a subtle off-by-one here; if `2 * concave_corners` is not
    # divisible by 4, we cut off half an edge. This seems to work, but why?
    return (corners + 2 * (area + edges - concave_corners)) // 4


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    instructions = [(distance, direction) for distance, direction, _ in read_input("input_test_2")]
    assert part_2(instructions) == 50
    instructions = [(distance, direction) for distance, direction, _ in read_input("input_test")]
    assert part_2(instructions) == EXPECTED_PART_1
    instructions = parse_hex_instructions(read_input("input_test"))
    assert part_2(instructions) == EXPECTED_PART_2


def main():
    instructions = list(read_input("input"))
    print(part_1(instructions))
    print(part_2(parse_hex_instructions(instructions)))


if __name__ == "__main__":
    main()
