#!/usr/bin/env python3

from attr import attrib
from attr import attrs

EXPECTED_PART_1 = "CMZ"
EXPECTED_PART_2 = "MCD"


@attrs(frozen=True)
class Move:
    amount = attrib()
    from_ = attrib()
    to = attrib()


def parse_stacks(lines):
    stack_count = len(lines[-1].split())
    stacks = [[] for _ in range(stack_count)]
    for line in reversed(lines[:-1]):
        for i in range(stack_count):
            container = line[i * 4 + 1]
            if container != " ":
                stacks[i].append(container)
    return stacks


def parse_move(line):
    _, amount, _, from_, _, to = line.split()
    return Move(int(amount), int(from_) - 1, int(to) - 1)


def read_input(filename):
    with open(filename) as lines:
        stacks, moves = lines.read().split("\n\n")
        moves = [parse_move(line) for line in moves.splitlines()]
        stacks = parse_stacks(stacks.splitlines())
        return stacks, moves


def test_part_1():
    assert part_1(*read_input("input_test")) == EXPECTED_PART_1


def test_part_2():
    assert part_2(*read_input("input_test")) == EXPECTED_PART_2


def part_1(stacks, moves):
    for move in moves:
        for _ in range(move.amount):
            stacks[move.to].append(stacks[move.from_].pop())
    return "".join(stack[-1] for stack in stacks)


def part_2(stacks, moves):
    for move in moves:
        stacks[move.to].extend(stacks[move.from_][-move.amount:])
        del stacks[move.from_][-move.amount:]
    return "".join(stack[-1] for stack in stacks)


def main():
    print(part_1(*read_input("input")))
    print(part_2(*read_input("input")))


if __name__ == "__main__":
    main()
