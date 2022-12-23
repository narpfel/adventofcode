#!/usr/bin/env pypy3

from itertools import product

EXPECTED_PART_1 = 2129920
EXPECTED_PART_2 = 99


def read_input(filename):
    with open(filename) as lines:
        return frozenset(
            (x, y)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
            if c == "#"
        )


def flat_neighbours(point):
    x, y = point
    yield x + 1, y
    yield x - 1, y
    yield x, y + 1
    yield x, y - 1


def generation(bugs):
    new_bugs = set()
    for point in product(range(5), repeat=2):
        neighbour_count = sum(neighbour in bugs for neighbour in flat_neighbours(point))
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


def generation_part_2(bugs):
    min_z = min(z for _, _, z in bugs)
    max_z = max(z for _, _, z in bugs)
    new_bugs = set()
    for point in product(range(5), range(5), range(min_z - 1, max_z + 2)):
        if point[:2] != (2, 2):
            neighbour_count = sum(neighbour in bugs for neighbour in fractal_neighbours(point))
            if (
                (point in bugs and neighbour_count == 1)
                or (point not in bugs and neighbour_count in (1, 2))
            ):
                new_bugs.add(point)
    return frozenset(new_bugs)


def fractal_neighbours(point):
    x, y, z = point

    if (x, y) == (2, 1):
        for x_inner in range(5):
            yield x_inner, 0, z + 1

    if (x, y) == (2, 3):
        for x_inner in range(5):
            yield x_inner, 4, z + 1

    if (x, y) == (1, 2):
        for y_inner in range(5):
            yield 0, y_inner, z + 1

    if (x, y) == (3, 2):
        for y_inner in range(5):
            yield 4, y_inner, z + 1

    for xn, yn in flat_neighbours((x, y)):
        if xn == -1:
            yield 1, 2, z - 1
        if yn == -1:
            yield 2, 1, z - 1
        if xn == 5:
            yield 3, 2, z - 1
        if yn == 5:
            yield 2, 3, z - 1
        yield xn, yn, z


def part_2(bugs, *, generation_count=200):
    assert (2, 2) not in bugs
    bugs = {(x, y, 0) for x, y in bugs}

    for _ in range(generation_count):
        bugs = generation_part_2(bugs)

    return len(bugs)


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def test_part_2():
    assert part_2(read_input("input_test"), generation_count=10) == EXPECTED_PART_2


def main():
    bugs = read_input("input")
    print(part_1(bugs))
    print(part_2(bugs))


if __name__ == "__main__":
    main()
