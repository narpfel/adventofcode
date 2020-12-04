#!/usr/bin/env python3

from functools import reduce
from itertools import count
from itertools import islice
from operator import mul


def count_encountered_trees(tree_map, dx, dy):
    return sum(
        line[(dx * x) % len(line)] == "#"
        for (x, line) in zip(count(), islice(tree_map, None, None, dy))
    )


def main():
    with open("input") as lines:
        tree_map = [line.strip() for line in lines]

    print(count_encountered_trees(tree_map, 3, 1))
    print(reduce(mul, (
        count_encountered_trees(tree_map, dx, dy)
        for dx, dy in [(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)]
    )))


if __name__ == "__main__":
    main()
