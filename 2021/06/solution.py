#!/usr/bin/env python3

from collections import deque
from itertools import groupby
from pathlib import Path


def reproduce(population, duration):
    for _ in range(duration):
        reproducing = population.popleft()
        population.append(reproducing)
        population[6] += reproducing


def main():
    time_to_fish_count = {
        time: len(list(fish))
        for time, fish in groupby(sorted(map(int, Path("input").read_text().split(","))))
    }
    population = deque(time_to_fish_count.get(t, 0) for t in range(9))

    reproduce(population, 80)
    print(sum(population))

    reproduce(population, 256 - 80)
    print(sum(population))


if __name__ == "__main__":
    main()
