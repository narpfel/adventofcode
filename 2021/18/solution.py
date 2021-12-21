#!/usr/bin/env pypy3

import ast
import json
from functools import reduce as fold
from itertools import chain
from itertools import permutations


def parse_impl(nested_number, level=0):
    for child in nested_number:
        # match child:
        #     case int():
        #         yield child, level
        #     case [int(x), int(y)]:
        #         yield x, level + 1
        #         yield y, level + 1
        #     case list():
        #         yield from parse_impl(child, level + 1)
        #     case _:
        #         assert False
        if isinstance(child, int):
            yield child, level
        elif isinstance(child, list):
            if len(child) == 2 and isinstance(child[0], int) and isinstance(child[1], int):
                yield child[0], level + 1
                yield child[1], level + 1
            else:
                yield from parse_impl(child, level + 1)
        else:
            assert False


def parse(nested_number):
    return list(parse_impl(nested_number))


def reduce_step_explode(number):
    new_number = []
    changed = False
    number_iter = iter(number)
    for x, level in number_iter:
        if level >= 4:
            assert level == 4
            changed = True

            y, other_level = next(number_iter)
            assert other_level == 4

            try:
                rightmost_before, level_before = new_number.pop()
            except IndexError:
                pass
            else:
                new_number.append((rightmost_before + x, level_before))

            assert level == 4
            new_number.append((0, level - 1))

            try:
                leftmost_after, level_after = next(number_iter)
            except StopIteration:
                pass
            else:
                new_number.append((leftmost_after + y, level_after))

            break
        else:
            new_number.append((x, level))

    if changed:
        new_number.extend(number_iter)

    return changed, new_number


def reduce_step_split(number):
    new_number = []
    changed = False
    number_iter = iter(number)
    for x, level in number_iter:
        if x >= 10:
            changed = True
            new_number.append((x // 2, level + 1))
            new_number.append(((x + 1) // 2, level + 1))
            break
        else:
            new_number.append((x, level))

    if changed:
        new_number.extend(number_iter)

    return changed, new_number


def reduce_step(number):
    changed, new_number = reduce_step_explode(number)
    if not changed:
        changed, new_number = reduce_step_split(new_number)

    return changed, new_number


def reduce(number):
    while True:
        changed, new_number = reduce_step(number)
        if not changed:
            assert new_number == number
            return new_number
        number = new_number


def add(a, b):
    return reduce([(x, level + 1) for x, level in chain(a, b)])


def unflatten(number):
    lengths = []
    result = ["["]

    for x, target_level in number:
        while lengths and lengths[-1] == 2:
            result.append("],")
            lengths.pop()
        while len(lengths) < target_level:
            if lengths:
                lengths[-1] += 1
            result.append("[")
            lengths.append(0)
        while len(lengths) > target_level:
            result.append("],")
            lengths.pop()

        while len(lengths) < target_level:
            if lengths:
                lengths[-1] += 1
            result.append("[")
            lengths.append(0)
        result.append(f"{x},")
        if lengths:
            lengths[-1] += 1

    for _ in lengths:
        result.append("],")

    result.append("]")

    return ast.literal_eval("".join(result))


def magnitude(number):
    def go(number):
        # match number:
        #     case int():
        #         return number
        #     case [x, y]:
        #         return 3 * go(x) + 2 * go(y)
        #     case _:
        #         assert False
        if isinstance(number, int):
            return number
        elif isinstance(number, list) and len(number) == 2:
            return 3 * go(number[0]) + 2 * go(number[1])
        else:
            assert False
    return go(unflatten(number))


def main():
    with open("input") as lines:
        snailfish_numbers = [parse(json.loads(line.strip())) for line in lines]

    result = fold(add, snailfish_numbers)
    print(magnitude(result))
    print(max(magnitude(add(a, b)) for a, b in permutations(snailfish_numbers, 2)))


if __name__ == "__main__":
    main()
