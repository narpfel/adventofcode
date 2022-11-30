#!/usr/bin/env pypy3

from collections import defaultdict
from itertools import count

TARGET_DURATION_PART_2 = 1000000000


def step(area):
    result = [list(line) for line in area]

    for y, line in enumerate(area):
        for x, tile in enumerate(line):
            neighbour_counts = defaultdict(int)
            for x_n, y_n in neighbours(x, y):
                if x_n in range(len(line)) and y_n in range(len(area)):
                    neighbour_counts[area[y_n][x_n]] += 1
            if tile == "." and neighbour_counts["|"] >= 3:
                new_tile = "|"
            elif tile == "|" and neighbour_counts["#"] >= 3:
                new_tile = "#"
            elif tile == "#":
                if neighbour_counts["|"] >= 1 and neighbour_counts["#"] >= 1:
                    new_tile = "#"
                else:
                    new_tile = "."
            else:
                new_tile = tile
            result[y][x] = new_tile

    return result


def neighbours(x, y):
    return [
        (x - 1, y - 1),
        (x, y - 1),
        (x + 1, y - 1),
        (x - 1, y),
        (x + 1, y),
        (x - 1, y + 1),
        (x, y + 1),
        (x + 1, y + 1),
    ]


def resource_value(area):
    wood = sum(tile == "|" for line in area for tile in line)
    lumberyards = sum(tile == "#" for line in area for tile in line)
    return wood * lumberyards


def main():
    with open("input") as lines:
        initial_area = [list(line.strip()) for line in lines]

    area = initial_area
    seen = {}
    configurations = []
    for i in count():
        area = tuple(tuple(line) for line in area)
        configurations.append(area)
        if area in seen:
            break
        seen[area] = i
        area = step(area)
    cycle_start = seen[area]
    cycle_length = i - cycle_start
    target_index = cycle_start + ((TARGET_DURATION_PART_2 - cycle_start) % cycle_length)

    print(resource_value(configurations[10]))
    print(resource_value(configurations[target_index]))


if __name__ == "__main__":
    main()
