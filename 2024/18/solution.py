#!/usr/bin/env python3

from heapq import heappop
from heapq import heappush

EXPECTED_PART_1 = 22
EXPECTED_PART_2 = "6,1"

DIRECTIONS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(part) for part in line.split(",")) for line in lines]


def move(p, δp):
    x, y = p
    δx, δy = δp
    return x + δx, y + δy


class Unreachable(Exception):
    pass


def find_path(falling_bytes, count=1024, size=70):
    blocked = set(falling_bytes[:count])
    start = 0, 0
    end = size, size

    q = [(0, start, None)]
    visited = {}
    while q:
        d, p, prev = heappop(q)
        if p in visited:
            continue
        visited[p] = prev

        if p == end:
            path = {end}
            while True:
                p = visited[p]
                if p is None:
                    break
                path.add(p)
            return d, path

        for direction in DIRECTIONS:
            new_p = x, y = move(p, direction)
            if new_p not in blocked and x in range(size + 1) and y in range(size + 1):
                heappush(q, (d + 1, new_p, p))

    raise Unreachable


def part_1(falling_bytes, count=1024, size=70):
    return find_path(falling_bytes, count, size)[0]


def part_2(falling_bytes, count=1024, size=70):
    _, path = find_path(falling_bytes, count, size)

    for i in range(count, len(falling_bytes)):
        if falling_bytes[i - 1] in path:
            try:
                _, path = find_path(falling_bytes, i, size)
            except Unreachable:
                return ",".join(map(str, falling_bytes[i - 1]))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input, count=12, size=6) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input, count=12, size=6) == EXPECTED_PART_2


def main():
    falling_bytes = read_input("input")
    print(part_1(falling_bytes))
    print(part_2(falling_bytes))


if __name__ == "__main__":
    main()
