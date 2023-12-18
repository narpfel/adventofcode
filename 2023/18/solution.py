#!/usr/bin/env python3

EXPECTED_PART_1 = 62


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            direction, distance, colour = line.split()
            yield int(distance), direction, colour.strip("#()")


def move(point, *, direction):
    x, y = point
    match direction:
        case "R" | 0:
            x += 1
        case "D" | 1:
            y += 1
        case "L" | 2:
            x -= 1
        case "U" | 3:
            y -= 1
        case _:
            assert False, "unreachable"
    return x, y


def neighbours(point):
    x, y = point
    return [
        (x - 1, y),
        (x + 1, y),
        (x, y - 1),
        (x, y + 1),
    ]


def part_1(instructions):
    point = 0, 0
    path = {point}
    for distance, direction, _ in instructions:
        for _ in range(distance):
            point = move(point, direction=direction)
            path.add(point)

    min_x = min(x for x, _ in path) - 2
    max_x = max(x for x, _ in path) + 3
    min_y = min(y for _, y in path) - 2
    max_y = max(y for _, y in path) + 3
    x_range = range(min_x, max_x)
    y_range = range(min_y, max_y)

    # floodfill
    seen = set()
    next_points = [(min_x, min_y)]

    while next_points:
        point = next_points.pop()
        if point not in seen:
            seen.add(point)
            for neighbour in neighbours(point):
                x, y = neighbour
                if x in x_range and y in y_range and neighbour not in path:
                    next_points.append(neighbour)

    length = max_x - min_x
    width = max_y - min_y
    total_area = length * width

    return total_area - len(seen)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    instructions = list(read_input("input"))
    print(part_1(instructions))


if __name__ == "__main__":
    main()
