#!/usr/bin/env python3

from collections import Counter
from itertools import chain
from itertools import product
from pathlib import Path


def parse_point(s):
    return tuple(int(x) for x in s.split(","))


def parse_line(line):
    start, _, end = line.partition(" -> ")
    start_x, start_y = parse_point(start)
    end_x, end_y = parse_point(end)
    if start_x == end_x or start_y == end_y:
        return product(
            range(min(start_x, end_x), max(start_x, end_x) + 1),
            range(min(start_y, end_y), max(start_y, end_y) + 1),
        ), []
    else:
        x_dir = 1 if start_x < end_x else -1
        y_dir = 1 if start_y < end_y else -1
        return [], zip(
            range(start_x, end_x + x_dir, x_dir),
            range(start_y, end_y + y_dir, y_dir),
        )


def main():
    horizontal_vertical_lines, diagonal_lines = zip(
        *(
            parse_line(line)
            for line in Path("input").read_text().splitlines()
        ),
    )
    covered_points_horizontal_vertical = Counter(chain.from_iterable(horizontal_vertical_lines))
    covered_points_diagonal = Counter(chain.from_iterable(diagonal_lines))
    covered_points = covered_points_horizontal_vertical + covered_points_diagonal
    print(sum(overlap > 1 for overlap in covered_points_horizontal_vertical.values()))
    print(sum(overlap > 1 for overlap in covered_points.values()))


if __name__ == "__main__":
    main()
