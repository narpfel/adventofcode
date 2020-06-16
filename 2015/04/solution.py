#!/usr/bin/env python3
from hashlib import md5
from itertools import count

INPUT = b"iwrupvqb"


def lowest_with_n_zeroes(leading_zeroes):
    for n in count():
        hash = md5()
        hash.update(INPUT + str(n).encode())
        if hash.hexdigest().startswith("0" * leading_zeroes):
            return n


def main():
    print(lowest_with_n_zeroes(5))
    print(lowest_with_n_zeroes(6))


if __name__ == "__main__":
    main()
