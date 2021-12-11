#!/usr/bin/env python3

PARENS = dict(["()", "[]", "{}", "<>"])
OPENING = frozenset(PARENS.keys())
CLOSING = frozenset(PARENS.values())
ERROR_SCORE = {
    ")": 3,
    "]": 57,
    "}": 1197,
    ">": 25137,
}


def first_mismatch(line):
    open = []
    for c in line:
        if c in OPENING:
            open.append(c)
        elif c in CLOSING:
            expected = open.pop()
            if PARENS[expected] != c:
                return c
        else:
            raise AssertionError(f"unexpected character {c!r}")
    return None


def main():
    with open("input") as lines:
        lines = [line.strip() for line in lines]

    syntax_error_score = sum(ERROR_SCORE.get(first_mismatch(line), 0) for line in lines)
    print(syntax_error_score)


if __name__ == "__main__":
    main()
