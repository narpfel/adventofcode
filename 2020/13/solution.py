#!/usr/bin/env python3

from itertools import count

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


def solve_part2(busses):
    # Implementation of this algorithm:
    # https://en.wikipedia.org/w/index.php?title=Chinese_remainder_theorem&oldid=993982536#Search_by_sieving
    n = busses[0]
    x = 0
    for i, bus in filter(lambda ibus: ibus[1] is not UNSPECIFIED, enumerate(busses[1:], 1)):
        for _ in count():
            x += n
            if (x + i) % bus == 0:
                n *= bus
                break
    return x


def test_part1():
    assert solve_part1(*read_input("input_test")) == 295


@pytest.mark.parametrize("busses, expected", [
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
])
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
