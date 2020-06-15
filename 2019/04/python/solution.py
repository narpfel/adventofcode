#!/usr/bin/env pypy3
from itertools import groupby
from itertools import tee

INPUT = "246515-739105"


def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)


def iterator_len(iterator):
    return sum(1 for _ in iterator)


def is_valid(password, password_range):
    password_str = str(password)
    return (
        len(password_str) == 6
        and password in password_range
        and any(x == y for (x, y) in pairwise(password_str))
        and all(x <= y for (x, y) in pairwise(password_str))
    )


def part2_constraint(password):
    return any(iterator_len(group) == 2 for (_, group) in groupby(str(password)))


def main():
    password_range = range(*map(int, INPUT.split("-")))
    valid_passwords = [p for p in password_range if is_valid(p, password_range)]
    print(len(valid_passwords))
    print(iterator_len(p for p in valid_passwords if part2_constraint(p)))


if __name__ == "__main__":
    main()
