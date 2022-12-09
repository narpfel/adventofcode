#!/usr/bin/env python3

EXPECTED_PART_1 = 13
EXPECTED_PART_2 = 36

ROPE_LENGTH = 10


def parse_step(line):
    direction, amount = line.split()
    return direction, int(amount)


def read_input(filename):
    with open(filename) as lines:
        return [parse_step(line) for line in lines]


def move(point, direction):
    x, y = point

    if direction == "U":
        return x, y + 1
    elif direction == "D":
        return x, y - 1
    elif direction == "L":
        return x - 1, y
    elif direction == "R":
        return x + 1, y

    assert False, "unreachable"


def follow(head, tail):
    head_x, head_y = head
    tail_x, tail_y = tail

    if head_x == tail_x:
        # vertical rule
        if head_y - tail_y > 1:
            tail_y += 1
        elif head_y - tail_y < -1:
            tail_y -= 1
    elif head_y == tail_y:
        # horizontal rule
        if head_x - tail_x > 1:
            tail_x += 1
        elif head_x - tail_x < -1:
            tail_x -= 1
    elif abs(head_y - tail_y) + abs(head_x - tail_x) > 2:
        # diagonal rule
        if head_y > tail_y:
            tail_y += 1
        elif head_y < tail_y:
            tail_y -= 1
        if head_x > tail_x:
            tail_x += 1
        elif head_x < tail_x:
            tail_x -= 1

    return tail_x, tail_y


def move_rope(steps, recorded_positions):
    rope = [(0, 0)] * ROPE_LENGTH
    visited = {position: {(0, 0)} for position in recorded_positions}

    for direction, n in steps:
        for _ in range(n):
            rope[0] = move(rope[0], direction)

            for i in range(len(rope) - 1):
                rope[i + 1] = follow(rope[i], rope[i + 1])

            for position in recorded_positions:
                visited[position].add(rope[position])

    return tuple(len(visited[position]) for position in recorded_positions)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert move_rope(puzzle_input, (1,)) == (EXPECTED_PART_1,)


def test_part_2():
    puzzle_input = read_input("input_test")
    assert move_rope(puzzle_input, (9,)) == (1,)
    puzzle_input = read_input("input_test_2")
    assert move_rope(puzzle_input, (9,)) == (EXPECTED_PART_2,)


def main():
    steps = read_input("input")
    part_1, part_2 = move_rope(steps, (1, 9))
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
