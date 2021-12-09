#!/usr/bin/env pypy3

def fuel_consumption_part_1(start, end):
    return abs(start - end)


def fuel_consumption_part_2(start, end):
    distance = abs(start - end)
    return distance * (distance + 1) // 2


def main():
    with open("input") as file:
        positions = list(map(int, file.read().split(",")))

    possible_destinations = range(min(positions), max(positions) + 1)

    for fuel_consumption in [fuel_consumption_part_1, fuel_consumption_part_2]:
        print(
            min(
                sum(fuel_consumption(destination, position) for position in positions)
                for destination in possible_destinations
            ),
        )


if __name__ == "__main__":
    main()
