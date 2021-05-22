#!/usr/bin/env pypy3

import sys

if sys.version_info < (3,):
    range = xrange  # noqa: F821 (python2 only)


INPUT = "16,12,1,0,15,7,11"


def parse_input(starting_numbers):
    return [int(n) for n in starting_numbers.split(",")]


def solve(starting_numbers, turn_count):
    # lists of tuples use `ObjectListStrategy` even when all tuples are the
    # same size and contain only ints. Manually unpacking the tuple into two
    # ints therefore improves performance by 5x.
    number_to_turns = [-1, -1] * turn_count
    for i, n in enumerate(starting_numbers):
        number_to_turns[2 * n] = i
        number_to_turns[2 * n + 1] = -1
    last_spoken = starting_numbers[-1]

    for turn in range(len(starting_numbers), turn_count):
        x = number_to_turns[2 * last_spoken]
        y = number_to_turns[2 * last_spoken + 1]
        if y == -1:
            last_spoken = 0
        else:
            last_spoken = x - y
        x = number_to_turns[2 * last_spoken]
        number_to_turns[2 * last_spoken] = turn
        number_to_turns[2 * last_spoken + 1] = x

    return last_spoken


def main():
    print(solve(parse_input(INPUT), 2020))
    print(solve(parse_input(INPUT), 30 * 10**6))


def rpython_main(argv):
    main()
    return 0


def target(*args):
    return rpython_main


if __name__ == "__main__":
    main()
