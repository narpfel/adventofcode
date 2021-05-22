#!/usr/bin/env pypy3

# `_md5` is *way* faster than `hashlib.md5`, especially on PyPy, where the
# `hashlib` implementation has to go through FFI, whereas `_md5` is implemented
# in RPython.
from itertools import count

from _md5 import md5

INPUT = b"iwrupvqb"


def lowest_with_n_zeroes(leading_zeroes_count):
    leading_zeroes = "0" * leading_zeroes_count
    for n in count():
        hash = md5(INPUT + str(n).encode())
        if hash.hexdigest().startswith(leading_zeroes):
            return n


def main():
    print(lowest_with_n_zeroes(5))
    print(lowest_with_n_zeroes(6))


if __name__ == "__main__":
    main()
