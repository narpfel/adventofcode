#!/usr/bin/env pypy3

from pathlib import Path


def fuel_consumption_part_1(start, end):
    return abs(start - end)


def fuel_consumption_part_2(start, end):
    distance = abs(start - end)
    return distance * (distance + 1) // 2


def main():
    positions = list(map(int, Path("input").read_text().split(",")))
    for fuel_consumption in [fuel_consumption_part_1, fuel_consumption_part_2]:
        print(
            min(
                sum(fuel_consumption(destination, position) for position in positions)
                for destination in range(min(positions), max(positions))
            ),
        )


if __name__ == "__main__":
    main()
