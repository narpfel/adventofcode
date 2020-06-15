#!/usr/bin/env python3
from itertools import chain
from itertools import combinations


def main():
    with open("input") as lines:
        containers = list(map(int, lines))

    possibilities = list(chain.from_iterable(
        (cs for cs in combinations(containers, length) if sum(cs) == 150)
        for length in range(len(containers))
    ))
    print(len(possibilities))

    print(min(map(len, possibilities)))


if __name__ == '__main__':
    main()
