#!/usr/bin/env python3

from itertools import product

EXPECTED_PART_1 = 2129920


def read_input(filename):
    with open(filename) as lines:
        return frozenset(
            (x, y)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
            if c == "#"
        )


def neighbours(point):
    x, y = point
    yield x + 1, y
    yield x - 1, y
    yield x, y + 1
    yield x, y - 1


def generation(bugs):
    new_bugs = set()
    for point in product(range(5), repeat=2):
        neighbour_count = sum(neighbour in bugs for neighbour in neighbours(point))
        if (
            (point in bugs and neighbour_count == 1)
            or (point not in bugs and neighbour_count in (1, 2))
        ):
            new_bugs.add(point)
    return frozenset(new_bugs)


def part_1(bugs):
    seen = set()

    while bugs not in seen:
        seen.add(bugs)
        bugs = generation(bugs)

    return sum(
        2 ** i
        for i, (y, x) in enumerate(product(range(5), repeat=2))
        if (x, y) in bugs
    )


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
