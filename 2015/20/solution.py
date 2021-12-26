#!/usr/bin/env pypy3
from itertools import count

import sympy


def main():
    part_1_solved = False
    for n in count(1):
        divisors = sympy.divisors(n)
        if not part_1_solved and 10 * sum(divisors) >= 36_000_000:
            print("Solution (part 1):", n)
            part_1_solved = True
        if 11 * sum(div for div in divisors if n / div <= 50) >= 36_000_000:
            print("Solution (part 2):", n)
            break


if __name__ == "__main__":
    main()
