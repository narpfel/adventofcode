#!/usr/bin/env python3

from pathlib import Path

from more_itertools import windowed


def solve(numbers, *, window_len):
    return sum(sum(b) > sum(a) for a, b in windowed(windowed(numbers, window_len), 2))


def main():
    numbers = list(map(int, Path("input").read_text().splitlines()))
    print(solve(numbers, window_len=1))
    print(solve(numbers, window_len=3))


if __name__ == "__main__":
    main()
