#!/usr/bin/env python3

import json
from functools import cmp_to_key
from itertools import chain

EXPECTED_PART_1 = 13
EXPECTED_PART_2 = 140


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            line = line.strip()
            if line:
                yield json.loads(line)


def compare(left, right):
    match (left, right):
        case int(), int():
            return left - right
        case int(), list():
            return compare([left], right)
        case list(), int():
            return compare(left, [right])
        case list(), list():
            for x, y in zip(left, right):
                result = compare(x, y)
                if result != 0:
                    return result
            return compare(len(left), len(right))


def pairs(iterable):
    iterable = iter(iterable)
    yield from zip(iterable, iterable)


def part_1(packets):
    return sum(
        i
        for i, (left, right) in enumerate(pairs(packets), 1)
        if compare(left, right) < 0
    )


def part_2(packets):
    packets = sorted(chain(packets, [[[2]], [[6]]]), key=cmp_to_key(compare))
    return (packets.index([[2]]) + 1) * (packets.index([[6]]) + 1)


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def test_part_2():
    assert part_2(read_input("input_test")) == EXPECTED_PART_2


def main():
    packets = list(read_input("input"))
    print(part_1(packets))
    print(part_2(packets))


if __name__ == "__main__":
    main()
