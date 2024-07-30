#!/usr/bin/env pypy3

# `_md5` is *way* faster than `hashlib.md5`, especially on PyPy, where the
# `hashlib` implementation has to go through FFI, whereas `_md5` is implemented
# in RPython.
from itertools import count

from _md5 import md5

INPUT = b"iwrupvqb"


def find_hash_lower_than(maximum_value):
    for n in count():
        hash = md5(INPUT + str(n).encode())
        if hash.digest() < maximum_value:
            return n


def main():
    print(find_hash_lower_than(b"\x00\x00\x10"))
    print(find_hash_lower_than(b"\x00\x00\x01"))


if __name__ == "__main__":
    main()
