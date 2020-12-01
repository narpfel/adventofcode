#!/usr/bin/env python3

from itertools import combinations


def main():
    with open("input") as lines:
        expenses = list(map(int, lines))

    for a, b in combinations(expenses, 2):
        if a + b == 2020:
            print(a * b)
            break

    for a, b, c in combinations(expenses, 3):
        if a + b + c == 2020:
            print(a * b * c)
            break


if __name__ == "__main__":
    main()
