#!/usr/bin/env python3

import re

EXPECTED_PART_1 = 480

NUMBER_RE = re.compile(r"\d+")


def read_input(filename):
    with open(filename) as lines:
        for chunk in lines.read().split("\n\n"):
            ax, ay, bx, by, px, py = NUMBER_RE.findall(chunk)
            yield (
                (int(ax), int(ay)),
                (int(bx), int(by)),
                (int(px), int(py)),
            )


def part_1(machines):
    return sum(
        min(
            (
                3 * n + m
                for n in range(101)
                for m in range(101)
                if n * ax + m * bx == px and n * ay + m * by == py
            ),
            default=0,
        )
        for (ax, ay), (bx, by), (px, py) in machines
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
