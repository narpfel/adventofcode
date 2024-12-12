#!/usr/bin/env python3

EXPECTED_PART_1 = 1930


def neighbours(x, y):
    yield x - 1, y
    yield x + 1, y
    yield x, y - 1
    yield x, y + 1


def neighbours_in(garden, x, y):
    for neighbour in neighbours(x, y):
        if neighbour in garden:
            yield neighbour


def find_region_containing(garden, x, y):
    plant_ty = garden[x, y]
    to_visit = [(x, y)]
    region = {(x, y)}
    while to_visit:
        p = to_visit.pop()
        for neighbour in neighbours_in(garden, *p):
            if garden[neighbour] == plant_ty and neighbour not in region:
                region.add(neighbour)
                to_visit.append(neighbour)
    return frozenset(region)


def read_input(filename):
    with open(filename) as lines:
        garden = {}
        for y, line in enumerate(lines):
            for x, c in enumerate(line.strip()):
                garden[x, y] = c

    regions = set()
    not_in_any_region_yet = set(garden)
    while not_in_any_region_yet:
        x, y = not_in_any_region_yet.pop()
        region = find_region_containing(garden, x, y)
        not_in_any_region_yet -= region
        regions.add(region)

    return garden, regions


def border_len(garden, region):
    plant_ty = garden[next(iter(region))]
    return sum(
        garden.get(neighbour) != plant_ty
        for x, y in region
        for neighbour in neighbours(x, y)
    )


def part_1(puzzle_input):
    garden, regions = puzzle_input
    return sum(
        len(region) * border_len(garden, region)
        for region in regions
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
