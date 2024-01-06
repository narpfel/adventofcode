#!/usr/bin/env pypy3

import json
from functools import reduce as fold
from itertools import chain
from itertools import permutations


def parse_impl(nested_number, level=0):
    for child in nested_number:
        match child:
            case int():
                yield child, level
            case [int(x), int(y)]:
                yield x, level + 1
                yield y, level + 1
            case list():
                yield from parse_impl(child, level + 1)
            case _:
                assert False


def parse(nested_number):
    return list(parse_impl(nested_number))


def reduce_step_explode(number):
    changed = False

    i = 0
    while i < len(number):
        x, level = number[i]
        if level >= 4:
            assert level == 4
            changed = True

            y, other_level = number[i + 1]
            assert other_level == 4

            if i > 0:
                rightmost_before, level_before = number[i - 1]
                number[i - 1] = rightmost_before + x, level_before

            if i < len(number) - 2:
                leftmost_after, level_after = number[i + 2]
                number[i + 2] = leftmost_after + y, level_after

            number[i:i + 2] = [(0, level - 1)]
        else:
            i += 1

    return changed


def reduce_step_split(number):
    for i, (x, level) in enumerate(number):
        if x >= 10:
            number[i:i + 1] = [
                (x // 2, level + 1),
                ((x + 1) // 2, level + 1),
            ]
            return True

    return False


def reduce_step(number):
    changed = reduce_step_explode(number)
    if not changed:
        changed = reduce_step_split(number)
    return changed


def reduce(number):
    while True:
        changed = reduce_step(number)
        if not changed:
            return number


def add(a, b):
    return reduce([(x, level + 1) for x, level in chain(a, b)])


def magnitude(number):
    magnitude_stack = []
    lengths = [0]

    for x, level in number:
        level += 1
        while len(lengths) > level or lengths[-1] == 2:
            rhs = magnitude_stack.pop()
            lhs = magnitude_stack.pop()
            magnitude_stack.append(3 * lhs + 2 * rhs)
            lengths.pop()
        while len(lengths) < level:
            lengths[-1] += 1
            lengths.append(0)
        magnitude_stack.append(x)
        lengths[-1] += 1

    for _ in lengths:
        rhs = magnitude_stack.pop()
        lhs = magnitude_stack.pop()
        magnitude_stack.append(3 * lhs + 2 * rhs)

    assert len(magnitude_stack) == 1
    return magnitude_stack[0]


def main():
    with open("input") as lines:
        snailfish_numbers = [parse(json.loads(line.strip())) for line in lines]

    result = fold(add, snailfish_numbers)
    print(magnitude(result))
    print(max(magnitude(add(a, b)) for a, b in permutations(snailfish_numbers, 2)))


if __name__ == "__main__":
    main()
