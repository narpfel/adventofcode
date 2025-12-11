#!/usr/bin/env python3

from functools import cache

EXPECTED_PART_1 = 5
EXPECTED_PART_2 = 2


def read_input(filename):
    with open(filename) as lines:
        connections = {}
        for line in lines:
            from_, _, tos = line.partition(": ")
            connections[from_] = frozenset(tos.split())
        return connections


def part_1(connections):
    path_count = 0
    todo = ["you"]
    while todo:
        p = todo.pop()
        if p == "out":
            path_count += 1
        else:
            todo.extend(connections[p])
    return path_count


def part_2(connections):
    @cache
    def count_paths(start, end):
        if start == end:
            return 1
        return sum(
            count_paths(p, end)
            for p in connections.get(start, [])
        )

    return (
        count_paths("svr", "dac") * count_paths("dac", "fft") * count_paths("fft", "out")
        + count_paths("svr", "fft") * count_paths("fft", "dac") * count_paths("dac", "out")
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test_2")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    connections = read_input("input")
    print(part_1(connections))
    print(part_2(connections))


if __name__ == "__main__":
    main()
