#!/usr/bin/env pypy3

from itertools import combinations
from itertools import pairwise

EXPECTED_PART_1 = 50
EXPECTED_PART_2 = 24


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(part) for part in line.split(",")) for line in lines]


def part_1(points):
    return max(
        (abs(x - X) + 1) * (abs(y - Y) + 1)
        for (x, y), (X, Y) in combinations(points, r=2)
    )


def outline(points):
    for (x, y), (X, Y) in pairwise(points):
        if x == X:
            for ny in range(min(y, Y), max(y, Y) + 1):
                yield x, ny
        elif y == Y:
            for nx in range(min(x, X), max(x, X) + 1):
                yield nx, y
        else:
            assert False, ((x, y), (X, Y))


def outline_outside(points):
    border = []
    outside = []
    for (x, y), (X, Y) in pairwise(points + [points[0]]):
        if x == X:
            dx = 1 if y < Y else -1
            for ny in range(min(y, Y), max(y, Y) + 1):
                border.append((x, ny))
                outside.append((x + dx, ny))
        elif y == Y:
            dy = -1 if x < X else 1
            for nx in range(min(x, X), max(x, X) + 1):
                border.append((nx, y))
                outside.append((nx, y + dy))
        else:
            assert False, ((x, y), (X, Y))
    border = set(border)
    outside = set(outside) - border
    border_x, border_y = next(iter(border))
    for x in range(border_x):
        if (x, border_y) in outside:
            break
        assert (x, y) not in border
    return outside


def rectangle_area(rectangle):
    (x, y), (X, Y) = rectangle
    return (abs(x - X) + 1) * (abs(y - Y) + 1)


def part_2(points):
    outside = outline_outside(points)
    for (x, y), (X, Y) in sorted(combinations(points, r=2), key=rectangle_area, reverse=True):
        corners = [(x, y), (x, Y), (X, Y), (X, y), (x, y)]
        if all(p not in outside for p in outline(corners)):
            return rectangle_area(((x, y), (X, Y)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    points = read_input("input")
    print(part_1(points))
    print(part_2(points))


if __name__ == "__main__":
    main()
