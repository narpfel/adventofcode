#!/usr/bin/env python3

from itertools import chain

EXPECTED_PART_1 = 21
EXPECTED_PART_2 = 8


def with_coords(trees):
    result = []
    for y, line in enumerate(trees):
        result.append([])
        for x, tree in enumerate(line):
            result[-1].append(((x, y), tree))
    return result


def read_input(filename):
    with open(filename) as lines:
        return with_coords((int(tree) for tree in line.strip()) for line in lines)


def iter_visible_from_left(trees):
    for line in trees:
        for i, ((x, y), tree) in enumerate(line):
            if all(left < tree for _, left in line[:i]):
                yield x, y


def part_1(trees):
    visible = set(
        chain(
            iter_visible_from_left(trees),
            iter_visible_from_left(list(reversed(line)) for line in trees),
            iter_visible_from_left(zip(*trees)),
            iter_visible_from_left(list(reversed(line)) for line in zip(*trees)),
        ),
    )
    return len(visible)


def scenic_score(tree, trees):
    (x, y), height = tree

    left = x
    for left in reversed(range(x)):
        if trees[y][left][1] >= height:
            break

    right = x
    for right in range(x + 1, len(trees[0])):
        if trees[y][right][1] >= height:
            break

    up = y
    for up in reversed(range(y)):
        if trees[up][x][1] >= height:
            break

    down = y
    for down in range(y + 1, len(trees)):
        if trees[down][x][1] >= height:
            break

    return (x - left) * (right - x) * (y - up) * (down - y)


def part_2(trees):
    return max(scenic_score(tree, trees) for line in trees for tree in line)


def test_part_1():
    trees = read_input("input_test")
    assert part_1(trees) == EXPECTED_PART_1


def test_part_2():
    trees = read_input("input_test")
    assert scenic_score(((2, 3), 5), trees) == EXPECTED_PART_2
    assert part_2(trees) == EXPECTED_PART_2


def main():
    trees = read_input("input")
    print(part_1(trees))
    print(part_2(trees))


if __name__ == "__main__":
    main()
