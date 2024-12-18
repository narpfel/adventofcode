#!/usr/bin/env python3

from heapq import heappop
from heapq import heappush

EXPECTED_PART_1 = 22

DIRECTIONS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(part) for part in line.split(",")) for line in lines]


def move(p, δp):
    x, y = p
    δx, δy = δp
    return x + δx, y + δy


def part_1(falling_bytes, count=1024, size=70):
    blocked = set(falling_bytes[:count])
    start = 0, 0
    end = size, size

    q = [(0, start)]
    seen = set()
    while q:
        d, p = heappop(q)
        if p in seen:
            continue
        seen.add(p)

        if p == end:
            return d

        for direction in DIRECTIONS:
            new_p = x, y = move(p, direction)
            if new_p not in blocked and x in range(size + 1) and y in range(size + 1):
                heappush(q, (d + 1, new_p))

    assert False, "unreachable"


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input, count=12, size=6) == EXPECTED_PART_1


def main():
    falling_bytes = read_input("input")
    print(part_1(falling_bytes))


if __name__ == "__main__":
    main()
