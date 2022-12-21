#!/usr/bin/env python3

from collections import deque
from operator import add
from operator import floordiv
from operator import mul
from operator import sub

EXPECTED_PART_1 = 152

OPERATIONS = {"+": add, "-": sub, "*": mul, "/": floordiv}


def parse_monkey(line):
    monkey, operation = line.split(": ")
    try:
        return monkey, int(operation)
    except ValueError:
        lhs, operator, rhs = operation.split()
        return monkey, (operator, lhs, rhs)


def read_input(filename):
    with open(filename) as lines:
        return dict(parse_monkey(line) for line in lines)


def part_1(monkeys):
    todo = deque(monkeys.items())
    done = {}

    while todo:
        match todo.popleft():
            case monkey, int(result):
                done[monkey] = result
            case monkey, (op, lhs, rhs) if lhs in done and rhs in done:
                done[monkey] = OPERATIONS[op](done[lhs], done[rhs])
            case not_done:
                todo.append(not_done)

    return done["root"]


def test_part_1():
    monkeys = read_input("input_test")
    assert part_1(monkeys) == EXPECTED_PART_1


def main():
    monkeys = read_input("input")
    print(part_1(monkeys))


if __name__ == "__main__":
    main()
