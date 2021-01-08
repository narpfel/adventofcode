#!/usr/bin/env pypy3
from itertools import tee

INPUT = "cqjxjnds"


def advance(iterable, steps):
    for _ in range(steps):
        next(iterable, None)


def nwise(iterable, n=2):
    iterables = tee(iterable, n)
    for steps, iterable in enumerate(iterables):
        advance(iterable, steps)
    return zip(*iterables)


def has_increasing_triple(s):
    return any(ord(a) + 2 == ord(b) + 1 == ord(c) for a, b, c in nwise(s, 3))


def has_no_iol(s):
    return not set(s) & set("iol")


def has_overlapping_equal_pairs(s):
    equal_pairs = 0
    pairs = nwise(s)
    for a, b in pairs:
        if a == b:
            equal_pairs += 1
            next(pairs, None)
    return equal_pairs >= 2


def is_valid(s):
    return all(
        pred(s) for pred in [
            has_increasing_triple, has_no_iol, has_overlapping_equal_pairs,
        ]
    )


def increment_password(s):
    s = [ord(letter) - ord("a") for letter in s]
    s[-1] += 1
    letters = []
    carry = 0
    for letter in reversed(s):
        letter += carry
        if letter >= 26:
            carry = letter // 26
            letter %= 26
        else:
            carry = 0
        letters.append(chr(letter + ord("a")))
    return "".join(map(str, reversed(letters)))


def next_password(s):
    while True:
        s = increment_password(s)
        if is_valid(s):
            return s


def main():
    new_password = next_password(INPUT)
    print(new_password)
    print(next_password(new_password))


if __name__ == "__main__":
    main()
