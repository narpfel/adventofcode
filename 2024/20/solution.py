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
            return path

        for d in DIRECTIONS:
            new_p = move(p, d)
            if racetrack.get(new_p) in "SE.":
                heappush(q, (cost + 1, new_p, p))

    assert False, "unreachable"


def part_1(racetrack):
    path = find_path(racetrack)

    savings = []
    for i, cheat_start in enumerate(path):
        for cheat_d in DIRECTIONS:
            cheat_end = move(move(cheat_start, cheat_d), cheat_d)
            try:
                j = path.index(cheat_end)
            except ValueError:
                pass
            else:
                savings.append(j - i - 2)

    return sum(saving >= 100 for saving in savings)


def main():
    racetrack = read_input("input")
    print(part_1(racetrack))


if __name__ == "__main__":
    main()
