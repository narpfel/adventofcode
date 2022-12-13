#!/usr/bin/env python3

import json

EXPECTED_PART_1 = 13


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


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def main():
    packets = read_input("input")
    print(part_1(packets))


if __name__ == "__main__":
    main()
