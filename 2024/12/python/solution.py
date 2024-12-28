#!/usr/bin/env python3

EXPECTED_PART_1 = 1930

DIRECTIONS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def neighbours(x, y):
    return [
        (x - 1, y),
        (x + 1, y),
        (x, y - 1),
        (x, y + 1),
    ]


def neighbours_in(garden, x, y):
    return [
        neighbour
        for neighbour in neighbours(x, y)
        if neighbour in garden
    ]


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


def border_tiles(garden, region):
    scale = 3
    return {
        (x * scale + dx, y * scale + dy)
        for x, y in region
        for dx in range(scale)
        for dy in range(scale)
        if any(
            (nx // scale, ny // scale) not in region
            for nx, ny in neighbours(x * scale + dx, y * scale + dy)
        )
    }


def move(p, δp):
    x, y = p
    δx, δy = δp
    return x + δx, y + δy


def direction(index):
    return DIRECTIONS[index % 4]


def left(index):
    return direction(index - 1)


def forward(index):
    return direction(index)


def right(index):
    return direction(index + 1)


def side_count(garden, region):
    border = border_tiles(garden, region)
    result = 0
    while border:
        start = min(border, key=lambda p: (p[1], p[0]))
        p = start
        direction = 0
        while True:
            border.discard(p)

            if move(p, left(direction)) in border:
                result += 1
                direction -= 1
            elif move(p, forward(direction)) in border:
                result += p == start
            elif move(p, right(direction)) in border:
                result += 1
                direction += 1
            else:
                break

            p = move(p, forward(direction))

            if p == start:
                break

    return result


def part_2(puzzle_input):
    garden, regions = puzzle_input
    return sum(
        len(region) * side_count(garden, region)
        for region in regions
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    assert part_2(read_input("input_test")) == 1206
    assert part_2(read_input("input_test_2")) == 80
    assert part_2(read_input("input_test_3")) == 436
    assert part_2(read_input("input_test_4")) == 236
    assert part_2(read_input("input_test_5")) == 368


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
