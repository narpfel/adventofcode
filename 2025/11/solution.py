#!/usr/bin/env python3

EXPECTED_PART_1 = 5


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


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    connections = read_input("input")
    print(part_1(connections))


if __name__ == "__main__":
    main()
