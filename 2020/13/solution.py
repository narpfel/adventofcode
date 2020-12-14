#!/usr/bin/env python3

from itertools import count


def read_input(filename):
    with open(filename) as lines:
        yield int(next(lines))
        yield [int(bus) for bus in next(lines).strip().split(",") if bus != "x"]


def solve(earliest_time, busses):
    return next(
        (time - earliest_time) * bus
        for time in count(earliest_time)
        for bus in busses
        if time % bus == 0
    )


def test_part1():
    assert solve(*read_input("input_test")) == 295


def main():
    earliest_time, busses = read_input("input")
    print(solve(earliest_time, busses))


if __name__ == "__main__":
    main()
