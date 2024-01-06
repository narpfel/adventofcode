#!/usr/bin/env python3

import math
from itertools import combinations
from itertools import count
from itertools import tee

import pytest

UNSPECIFIED = object()


def parse_busses(busses):
    return [
        UNSPECIFIED if bus == "x" else int(bus)
        for bus in busses.split(",")
    ]


def read_input(filename):
    with open(filename) as lines:
        yield int(next(lines))
        yield parse_busses(next(lines).strip())


def solve_part1(earliest_time, busses):
    time, bus = min(
        (
            bus * (earliest_time // bus + 1) if earliest_time % bus != 0 else earliest_time,
            bus,
        )
        for bus in busses
        if bus is not UNSPECIFIED
    )
    return (time - earliest_time) * bus


def chinese_remainder_theorem(ixs):
    # Implementation of this algorithm:
    # https://en.wikipedia.org/w/index.php?title=Chinese_remainder_theorem&oldid=993982536#Search_by_sieving
    ixs, ixs_copy = tee(ixs)

    xs = [x for _, x in ixs_copy]
    gcds = {math.gcd(a, b) for a, b in combinations(xs, 2)}
    assert gcds == {1}, f"numbers must be pairwise coprime, but gcds are {gcds}; numbers = {xs}"

    _, period = next(ixs)
    result = 0
    for i, x in ixs:
        for _ in count():
            result += period
            if (result + i) % x == 0:
                period *= x
                break
    return result


def solve_part2(busses):
    return chinese_remainder_theorem(
        (departure_time, bus)
        for departure_time, bus in enumerate(busses)
        if bus is not UNSPECIFIED
    )


def test_part1():
    assert solve_part1(*read_input("input_test")) == 295


@pytest.mark.parametrize(
    "busses, expected", [
        ("7,13", 77),
        ("7,x,17", 49),
        ("7,13,17", 168),
        ("7,13,17,29", 14091),
        ("7,13,x,x,59,x,31,19",  1068781),
        ("17,x,13,19", 3417),
        ("67,7,59,61", 754018),
        ("67,x,7,59,61", 779210),
        ("67,7,x,59,61", 1261476),
        ("1789,37,47,1889", 1_202_161_486),
    ],
)
def test_part2(busses, expected):
    parsed = parse_busses(busses)
    for i, bus in enumerate(parsed):
        print(i, bus, (expected + i) / bus if bus is not UNSPECIFIED else "unspecified")
    assert solve_part2(parse_busses(busses)) == expected


def main():
    earliest_time, busses = read_input("input")
    print(solve_part1(earliest_time, busses))
    print(solve_part2(busses))


if __name__ == "__main__":
    main()
