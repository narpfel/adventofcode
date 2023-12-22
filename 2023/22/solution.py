#!/usr/bin/env pypy3

EXPECTED_PART_1 = 5


def parse_point(s):
    return [int(coordinate) for coordinate in s.split(",")]


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            start, end = line.split("~")
            yield parse_point(start), parse_point(end)


def make_brick(start, end):
    (x, y, z), (X, Y, Z) = start, end
    return frozenset(
        (a, b, c)
        for a in range(x, X + 1)
        for b in range(y, Y + 1)
        for c in range(z, Z + 1)
    )


def move(brick):
    return frozenset((x, y, z - 1) for x, y, z in brick)


def settle(bricks, x_range, y_range):
    while True:
        new_bricks = []
        all_bricks = {
            (x, y, 0)
            for x in x_range
            for y in y_range
        }
        for i, brick in bricks:
            while True:
                moved = move(brick)
                if moved & all_bricks:
                    new_bricks.append((i, brick))
                    all_bricks |= brick
                    break
                else:
                    brick = moved

        if new_bricks == bricks:
            return new_bricks

        bricks = new_bricks


def solve(bricks):
    bricks = [(i, make_brick(start, end)) for i, (start, end) in enumerate(bricks)]
    bricks = sorted(bricks, key=lambda b: min(z for _, _, z in b[1]))

    min_x = min(x for _, brick in bricks for x, _, _ in brick)
    max_x = max(x for _, brick in bricks for x, _, _ in brick)
    min_y = min(y for _, brick in bricks for _, y, _ in brick)
    max_y = max(y for _, brick in bricks for _, y, _ in brick)
    x_range = range(min_x, max_x + 1)
    y_range = range(min_y, max_y + 1)

    bricks = settle(bricks, x_range, y_range)

    result = 0
    for i, brick in enumerate(bricks):
        copy = bricks[:i] + bricks[i + 1:]
        settled = frozenset(settle(copy, x_range, y_range))
        copy = frozenset(copy)

        if settled == copy:
            result += 1

    return result


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input) == EXPECTED_PART_1


def main():
    print(solve(read_input("input")))


if __name__ == "__main__":
    main()
