#!/usr/bin/env python3

from contextlib import suppress
from itertools import chain
from itertools import count
from itertools import product


class Octopus:
    def __init__(self, energy):
        self.energy = energy
        self.flashed = False

    def tick(self):
        if self.flashed:
            return False
        self.energy += 1
        if self.energy > 9:
            self.flashed = True
            return True
        else:
            return False


def neighbours(point):
    x, y = point
    for (Δx, Δy) in product([-1, 0, 1], repeat=2):
        a, b = x + Δx, y + Δy
        if (Δx or Δy) and a >= 0 and b >= 0:
            yield a, b


def main():
    with open("input") as lines:
        octopodes = [[Octopus(int(octopus)) for octopus in line.strip()] for line in lines]

    total_flash_count = 0

    for i in count():
        if i == 100:
            solution_part_1 = total_flash_count

        flashed = []

        for y, line in enumerate(octopodes):
            for x, octopus in enumerate(line):
                if octopus.tick():
                    flashed.append((x, y))

        while flashed:
            old_flashed = flashed
            flashed = []
            for point in old_flashed:
                for x, y in neighbours(point):
                    with suppress(IndexError):
                        if octopodes[y][x].tick():
                            flashed.append((x, y))

        all_flashed = True
        for octopus in chain.from_iterable(octopodes):
            if octopus.flashed:
                total_flash_count += 1
                octopus.energy = 0
                octopus.flashed = False
            else:
                all_flashed = False

        if all_flashed:
            solution_part_2 = i + 1
            break

    print(solution_part_1)
    print(solution_part_2)


if __name__ == "__main__":
    main()
