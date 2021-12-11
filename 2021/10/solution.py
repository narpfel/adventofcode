#!/usr/bin/env python3

from functools import reduce
from statistics import median

from more_itertools import partition

PARENS = dict(["()", "[]", "{}", "<>"])
OPENING = frozenset(PARENS.keys())
CLOSING = frozenset(PARENS.values())
ERROR_SCORE = {
    ")": 3,
    "]": 57,
    "}": 1197,
    ">": 25137,
}
AUTOCOMPLETE_SCORE = {
    ")": 1,
    "]": 2,
    "}": 3,
    ">": 4,
}


class Incomplete:
    def __init__(self, autocompletion):
        self.autocompletion = autocompletion

    @property
    def score(self):
        return reduce(lambda acc, c: 5 * acc + AUTOCOMPLETE_SCORE[c], self.autocompletion, 0)


class Corrupted:
    def __init__(self, mismatch):
        self.mismatch = mismatch

    @property
    def score(self):
        return ERROR_SCORE[self.mismatch]


def analyse(line):
    open = []
    for c in line:
        if c in OPENING:
            open.append(c)
        elif c in CLOSING:
            expected = open.pop()
            if PARENS[expected] != c:
                return Corrupted(c)
        else:
            raise AssertionError(f"unexpected character {c!r}")
    return Incomplete([PARENS[c] for c in reversed(open)])


def main():
    with open("input") as lines:
        lines = [line.strip() for line in lines]

    incomplete, corrupted = partition(
        lambda value: isinstance(value, Corrupted),
        map(analyse, lines),
    )

    syntax_error_score = sum(mismatch.score for mismatch in corrupted)
    print(syntax_error_score)
    autocomplete_score = median(autocompletion.score for autocompletion in incomplete)
    print(autocomplete_score)


if __name__ == "__main__":
    main()
