#!/usr/bin/env pypy3

from functools import cache
from heapq import heappop
from heapq import heappush

EXPECTED_PART_1 = 18
EXPECTED_PART_2 = 54


def read_input(filename):
    with open(filename) as lines:
        return frozenset(
            (x, y, c) for y, line in enumerate(lines)
            for x, c in enumerate(line)
            if c in "<>^v#"
        )


def move(blizzard, size_x, size_y):
    x, y, c = blizzard

    if c == "#":
        return x, y, c
    elif c == ">":
        return 1 if x == size_x - 1 else x + 1, y, c
    elif c == "<":
        return size_x - 1 if x == 1 else x - 1, y, c
    elif c == "^":
        return x, size_y - 1 if y == 1 else y - 1, c
    elif c == "v":
        return x, 1 if y == size_y - 1 else y + 1, c


def neighbours(x, y):
    return [
        (x, y),
        (x - 1, y),
        (x + 1, y),
        (x, y - 1),
        (x, y + 1),
    ]


@cache
def map_at_time(valley, time, size_x, size_y):
    if time == 0:
        return valley, frozenset((x, y) for x, y, _ in valley)
    elif time < 0:
        assert False

    valley, _ = map_at_time(valley, time - 1, size_x, size_y)
    result = set()
    for blizzard in valley:
        result.add(move(blizzard, size_x, size_y))

    return frozenset(result), frozenset((x, y) for x, y, _ in result)


def travel_time(initial_valley, *, start, target, time_offset):
    min_x = min(x for x, _, _ in initial_valley)
    max_x = max(x for x, _, _ in initial_valley)
    min_y = min(y for _, y, _ in initial_valley)
    max_y = max(y for _, y, _ in initial_valley)
    xrange = range(min_x, max_x + 1)
    yrange = range(min_y, max_y + 1)

    next_points = []
    heappush(next_points, (0, *start))
    to_visit = set()

    while next_points:
        time, x, y = heappop(next_points)
        to_visit.discard((x, y))

        if (x, y) == target:
            return time

        valley, occupied = map_at_time(initial_valley, time_offset + time + 1, max_x, max_y)

        for xn, yn in neighbours(x, y):
            if xn in xrange and yn in yrange and (xn, yn) not in occupied:
                if (xn, yn) not in to_visit:
                    to_visit.add((xn, yn))
                    heappush(next_points, (time + 1, xn, yn))

    assert False, "unreachable"


def part_1(valley):
    max_x = max(x for x, _, _ in valley)
    max_y = max(y for _, y, _ in valley)
    target = max_x - 1, max_y
    return travel_time(valley, start=(1, 0), target=target, time_offset=0)


def part_2(valley):
    max_x = max(x for x, _, _ in valley)
    max_y = max(y for _, y, _ in valley)
    target = max_x - 1, max_y
    there = travel_time(valley, start=(1, 0), target=target, time_offset=0)
    and_back = travel_time(valley, start=target, target=(1, 0), time_offset=there)
    and_back_again = travel_time(valley, start=(1, 0), target=target, time_offset=there + and_back)
    return there + and_back + and_back_again


def test_part_1():
    valley = read_input("input_test")
    assert part_1(valley) == EXPECTED_PART_1


def test_part_2():
    valley = read_input("input_test")
    assert part_2(valley) == EXPECTED_PART_2


def main():
    valley = read_input("input")
    print(part_1(valley))
    print(part_2(valley))


if __name__ == "__main__":
    main()
