#!/usr/bin/env python3

from itertools import count
from sympy import divisors


def main():
    part_1_solved = False
    for n in count(1):
        if 10 * sum(divisors(n, generator=True)) >= 36000000 and not part_1_solved:
            print("Solution (part 1):", n)
            part_1_solved = True
        if 11 * sum(div for div in divisors(n, generator=True) if n / div <= 50) >= 36000000:
            print("Solution (part 2):", n)
            break


if __name__ == '__main__':
    main()
