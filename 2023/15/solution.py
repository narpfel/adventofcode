#!/usr/bin/env python3

import re
from collections import defaultdict
from contextlib import suppress

EXPECTED_PART_1 = 1320
EXPECTED_PART_2 = 145

NAME_RE = re.compile(r"\w+")


def read_input(filename):
    with open(filename) as lines:
        return lines.read().strip().split(",")


def calculate_hash(s):
    hash_value = 0
    for c in s:
        hash_value += ord(c)
        hash_value *= 17
        hash_value %= 256
    return hash_value


def part_1(initialisation_sequence):
    return sum(calculate_hash(step) for step in initialisation_sequence)


def part_2(initialisation_sequence):
    boxes = defaultdict(dict)

    for operation in initialisation_sequence:
        name = NAME_RE.match(operation)[0]
        hash_value = calculate_hash(name)
        if "-" in operation:
            with suppress(KeyError):
                del boxes[hash_value][name]
        if "=" in operation:
            focus_length = int(operation.split("=")[1])
            boxes[hash_value][name] = focus_length

    return sum(
        (box_id + 1) * i * focus_length
        for box_id, box in boxes.items()
        for i, (_, focus_length) in enumerate(box.items(), 1)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    initialisation_sequence = read_input("input")
    print(part_1(initialisation_sequence))
    print(part_2(initialisation_sequence))


if __name__ == "__main__":
    main()
