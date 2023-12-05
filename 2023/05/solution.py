#!/usr/bin/env python3

from collections import namedtuple

EXPECTED_PART_1 = 35


Range = namedtuple("Range", "dest, src, len")


def read_input(filename):
    with open(filename) as lines:
        blocks = lines.read().split("\n\n")

    seeds = [int(x) for x in blocks[0].split(":")[-1].split()]
    maps = {}
    for block in blocks[1:]:
        lines = block.splitlines()
        from_, to = tuple(lines[0].split()[0].split("-to-"))
        ranges = [
            Range(*map(int, line.split()))
            for line in lines[1:]
        ]
        maps[from_, to] = ranges
    return seeds, maps


def part_1(seeds, maps):
    locations = []
    for seed in seeds:
        for map_ in maps.values():
            for range_ in map_:
                if seed in range(range_.src, range_.src + range_.len):
                    seed = seed - range_.src + range_.dest
                    break
        locations.append(seed)

    return min(locations)


def test_part_1():
    seeds, maps = read_input("input_test")
    assert part_1(seeds, maps) == EXPECTED_PART_1


def main():
    seeds, maps = read_input("input")
    print(part_1(seeds, maps))


if __name__ == "__main__":
    main()
