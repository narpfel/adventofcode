#!/usr/bin/env python3

from collections import deque
from operator import add
from operator import floordiv
from operator import mul
from operator import sub

EXPECTED_PART_1 = 152
EXPECTED_PART_2 = 301

OPERATIONS = {"+": add, "-": sub, "*": mul, "/": floordiv}
INVERSE_OPERATIONS_LHS = {"+": sub, "-": add, "*": floordiv, "/": mul}
INVERSE_OPERATIONS_RHS = {
    "+": sub,
    "-": lambda lhs, rhs: rhs - lhs,
    "*": floordiv,
    "/": lambda lhs, rhs: rhs // lhs,
}


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


def calculate_monkeys(monkeys):
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

    return done


def has_humn(monkeys, monkey):
    if monkey == "humn":
        return True

    match monkeys[monkey]:
        case int():
            return False
        case _, lhs, rhs:
            return has_humn(monkeys, lhs) or has_humn(monkeys, rhs)


def invert(monkeys, results, result, monkey):
    if monkey == "humn":
        return result

    op, lhs, rhs = monkeys[monkey]
    lhs_has_humn = has_humn(monkeys, lhs)
    rhs_has_humn = has_humn(monkeys, rhs)
    assert lhs_has_humn != rhs_has_humn

    if lhs_has_humn:
        return invert(monkeys, results, INVERSE_OPERATIONS_LHS[op](result, results[rhs]), lhs)
    elif rhs_has_humn:
        return invert(monkeys, results, INVERSE_OPERATIONS_RHS[op](result, results[lhs]), rhs)


def part_2(monkeys, results):
    _, lhs, rhs = monkeys["root"]
    lhs_has_humn = has_humn(monkeys, lhs)
    rhs_has_humn = has_humn(monkeys, rhs)
    assert lhs_has_humn != rhs_has_humn

    if lhs_has_humn:
        result = results[rhs]
        monkey = lhs
    else:
        result = results[lhs]
        monkey = rhs

    return invert(monkeys, results, result, monkey)


def test_part_1():
    monkeys = read_input("input_test")
    results = calculate_monkeys(monkeys)
    assert results["root"] == EXPECTED_PART_1


def test_part_2():
    monkeys = read_input("input_test")
    results = calculate_monkeys(monkeys)
    assert part_2(monkeys, results) == EXPECTED_PART_2


def main():
    monkeys = read_input("input")
    results = calculate_monkeys(monkeys)
    print(results["root"])
    print(part_2(monkeys, results))


if __name__ == "__main__":
    main()
