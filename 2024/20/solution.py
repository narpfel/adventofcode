#!/usr/bin/env pypy3

from heapq import heappop
from heapq import heappush

DIRECTIONS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def read_input(filename):
    with open(filename) as lines:
        return {
            (x, y): c
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
        }


def move(p, δp):
    x, y = p
    δx, δy = δp
    return x + δx, y + δy


def find_path(racetrack):
    start = next(p for p, t in racetrack.items() if t == "S")
    end = next(p for p, t in racetrack.items() if t == "E")
    q = [(0, start, None)]
    seen = {}
    while q:
        cost, p, prev = heappop(q)
        if p in seen:
            continue
        seen[p] = prev

        if p == end:
            path = [end]
            while True:
                p = seen[p]
                if p is None:
                    break
                path.append(p)
            path.reverse()

            walkable_tiles = {p for p, tile in racetrack.items() if tile in "SE."}
            assert walkable_tiles == set(path)

            return path

        for d in DIRECTIONS:
            new_p = move(p, d)
            if racetrack.get(new_p) in "SE.":
                heappush(q, (cost + 1, new_p, p))

    assert False, "unreachable"


def manhattan_distance(p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    return abs(x1 - x2) + abs(y1 - y2)


def solve(path, max_cheat_length):
    visited_points = {p: i for i, p in enumerate(path)}
    large_savings_count = 0
    for i, cheat_start in enumerate(path):
        for dy in range(-max_cheat_length, max_cheat_length + 1):
            x_range = max_cheat_length - abs(dy)
            for dx in range(-x_range, x_range + 1):
                cheat_end = move(cheat_start, (dx, dy))
                j = visited_points.get(cheat_end)
                if j is not None:
                    large_savings_count += (j - i - (abs(dx) + abs(dy))) >= 100

    return large_savings_count


def part_1(path):
    return solve(path, max_cheat_length=2)


def part_2(path):
    return solve(path, max_cheat_length=20)


def main():
    racetrack = read_input("input")
    path = find_path(racetrack)
    print(part_1(path))
    print(part_2(path))


if __name__ == "__main__":
    main()
