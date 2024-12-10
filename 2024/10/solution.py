#!/usr/bin/env python3

EXPECTED_PART_1 = 36
EXPECTED_PART_2 = 81


def read_input(filename):
    with open(filename) as lines:
        return {
            (x, y): 100 if c == "." else int(c)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
        }


def neighbours(x, y):
    return [
        (x - 1, y),
        (x + 1, y),
        (x, y - 1),
        (x, y + 1),
    ]


def find_end_points(start_point, height_map):
    points = [start_point]
    for height in range(9):
        new_points = []
        for x, y in points:
            for neighbour in neighbours(x, y):
                if height_map.get(neighbour) == height + 1:
                    new_points.append(neighbour)
        points = new_points
    return points


def solve(height_map, *, collect_end_points):
    return sum(
        len(collect_end_points(find_end_points(point, height_map)))
        for (point, height) in height_map.items()
        if height == 0
    )


def part_1(height_map):
    return solve(height_map, collect_end_points=set)


def part_2(height_map):
    return solve(height_map, collect_end_points=lambda end_points: end_points)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
