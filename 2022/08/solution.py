#!/usr/bin/env python3

from itertools import chain

EXPECTED_PART_1 = 21


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


def test_part_1():
    trees = read_input("input_test")
    assert part_1(trees) == EXPECTED_PART_1


def main():
    trees = read_input("input")
    print(part_1(trees))


if __name__ == "__main__":
    main()
