#!/usr/bin/env pypy3

EXPECTED_PART_1 = 5
EXPECTED_PART_2 = 7


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
    new_bricks = []
    all_blocks = {
        (x, y, 0)
        for x in x_range
        for y in y_range
    }
    for i, brick in bricks:
        while True:
            moved = move(brick)
            if moved & all_blocks:
                new_bricks.append((i, brick))
                all_blocks |= brick
                break
            else:
                brick = moved

    return new_bricks


def solve(bricks):
    bricks = [(i, make_brick(start, end)) for i, (start, end) in enumerate(bricks)]
    bricks = sorted(bricks, key=lambda brick: min(z for _, _, z in brick[1]))

    min_x = min(x for _, brick in bricks for x, _, _ in brick)
    max_x = max(x for _, brick in bricks for x, _, _ in brick)
    min_y = min(y for _, brick in bricks for _, y, _ in brick)
    max_y = max(y for _, brick in bricks for _, y, _ in brick)
    x_range = range(min_x, max_x + 1)
    y_range = range(min_y, max_y + 1)

    bricks = settle(bricks, x_range, y_range)

    result_part_1 = 0
    result_part_2 = 0
    for i, brick in enumerate(bricks):
        ith_brick_removed = bricks[:i] + bricks[i + 1:]
        settled = frozenset(settle(ith_brick_removed, x_range, y_range))
        ith_brick_removed = frozenset(ith_brick_removed)

        if settled == ith_brick_removed:
            result_part_1 += 1
        else:
            result_part_2 += len(settled - ith_brick_removed)

    return result_part_1, result_part_2


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[0] == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[1] == EXPECTED_PART_2


def main():
    part_1, part_2 = solve(read_input("input"))
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
