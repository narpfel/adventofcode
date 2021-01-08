#!/usr/bin/env python3

from itertools import permutations

import numpy as np


def main():
    numbers = np.loadtxt("input", dtype=np.int64)
    print((numbers.max(axis=1) - numbers.min(axis=1)).sum())

    print(
        sum(
            x // y
            for row in numbers
            for (x, y) in permutations(row, 2)
            if not x % y
        ),
    )


if __name__ == "__main__":
    main()
