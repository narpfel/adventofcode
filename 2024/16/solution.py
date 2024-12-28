#!/usr/bin/env python3

from heapq import heappop
from heapq import heappush

EXPECTED_PART_1 = 11048
EXPECTED_PART_2 = 64

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


def part_1(maze):
    start = next(p for p, t in maze.items() if t == "S")
    end = next(p for p, t in maze.items() if t == "E")
    q = [(0, start, 0)]
    seen = {}
    while q:
        cost, p, d = heappop(q)
        if (p, d) in seen and seen[p, d] <= cost:
            continue
        seen[p, d] = cost

        if p == end:
            return cost

        for additional_cost, δd in ((1, 0), (1001, -1), (1001, 1)):
            new_d = (d + δd) % 4
            new_p = move(p, DIRECTIONS[new_d])
            if maze.get(new_p) in "SE.":
                heappush(q, (cost + additional_cost, new_p, new_d))

    assert False, "unreachable"


def part_2(maze, max_cost):
    start = next(p for p, t in maze.items() if t == "S")
    end = next(p for p, t in maze.items() if t == "E")

    points = {(start, 0): (max_cost, [(start, 0)])}

    q = [(0, start, 0, (start, 0))]
    while q:
        cost, p, d, prev = heappop(q)
        if cost > max_cost:
            break

        known_minimal_cost, points_in_path = points.setdefault((p, d), (max_cost, []))
        if known_minimal_cost < cost:
            pass
        elif known_minimal_cost == cost:
            points_in_path.append(prev)
        else:
            points[p, d] = cost, [prev]
            prev = p, d

            for additional_cost, δd in ((1, 0), (1001, -1), (1001, 1)):
                new_d = (d + δd) % 4
                new_p = move(p, DIRECTIONS[new_d])
                if maze.get(new_p) in "SE.":
                    heappush(q, (cost + additional_cost, new_p, new_d, prev))

    points_on_any_path = set()
    todo = [(end, d) for d in range(4)]
    while todo:
        p, d = todo.pop()
        points_on_any_path.add((p, d))
        for p, d in points.get((p, d), (0, ()))[1]:
            if (p, d) not in points_on_any_path:
                todo.append((p, d))
    return len({p for p, _ in points_on_any_path})


def test_part_1():
    puzzle_input = read_input("input_test_2")
    assert part_1(puzzle_input) == 7036
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test_2")
    assert part_2(puzzle_input, part_1(puzzle_input)) == 45
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input, part_1(puzzle_input)) == EXPECTED_PART_2


def main():
    maze = read_input("input")
    best_path_cost = part_1(maze)
    print(best_path_cost)
    print(part_2(maze, best_path_cost))


if __name__ == "__main__":
    main()
