#!/usr/bin/env python3

import re
from itertools import chain


HYPERNET_SEQUENCE = re.compile(r"\[.*?\]")
ABBA_SEQUENCE = re.compile(r"(?P<a>[a-z])(?!(?P=a))(?P<b>[a-z])(?P=b)(?P=a)")
ABA_SEQUENCE = re.compile(r"(?P<a>[a-z])(?!(?P=a))?(?P<b>[a-z])(?P=a)")


def finditer_overlap(pattern, s):
    start = 0
    while True:
        match = pattern.search(s, start)
        if match:
            yield match
            start = match.start() + 1
        else:
            return


def has_abba(s):
    return ABBA_SEQUENCE.search(s)


def supports_tls(ip):
    return (
        any(has_abba(part) for part in HYPERNET_SEQUENCE.split(ip))
        and not any(has_abba(seq.group(0)) for seq in HYPERNET_SEQUENCE.finditer(ip))
    )


def supports_ssl(ip):
    supernet_sequences = HYPERNET_SEQUENCE.split(ip)
    hypernet_sequences = HYPERNET_SEQUENCE.findall(ip)
    for aba_sequence in chain.from_iterable(
            finditer_overlap(ABA_SEQUENCE, part) for part in supernet_sequences
    ):
        a, b, _ = aba_sequence.group(0)
        bab = f"{b}{a}{b}"
        if any(bab in part for part in hypernet_sequences):
            return True
    return False


def solve(solver, lines):
    return len(list(filter(solver, lines)))


def main():
    with open("input") as lines:
        lines = list(lines)

    print(solve(supports_tls, lines))
    print(solve(supports_ssl, lines))


if __name__ == "__main__":
    main()
