#!/usr/bin/env python3

from collections import namedtuple

import z3
from more_itertools import chunked

EXPECTED_PART_1 = 35
EXPECTED_PART_2 = 46


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


def part_2(seeds, maps):
    opt = z3.Optimize()

    values = {"seed": z3.Int("seed")} | {
        to: z3.Int(to)
        for _, to in maps
    }
    seed = values["seed"]

    constraints = [
        z3.And(seed >= seed_range[0], seed < seed_range[0] + seed_range[1])
        for seed_range in chunked(seeds, 2)
    ]
    opt.add(z3.Or(*constraints))

    for (from_, to), map_ in maps.items():
        from_value = values[from_]
        to_value = values[to]
        calculation = from_value == to_value
        for range_ in map_:
            calculation = z3.If(
                z3.And(from_value >= range_.src, from_value < range_.src + range_.len),
                to_value == from_value - range_.src + range_.dest,
                calculation,
            )
        opt.add(calculation)

    opt.minimize(values["location"])
    assert opt.check() == z3.sat
    model = opt.model()
    return model[values["location"]]


def test_part_1():
    seeds, maps = read_input("input_test")
    assert part_1(seeds, maps) == EXPECTED_PART_1


def test_part_2():
    seeds, maps = read_input("input_test")
    assert part_2(seeds, maps) == EXPECTED_PART_2


def main():
    seeds, maps = read_input("input")
    print(part_1(seeds, maps))
    print(part_2(seeds, maps))


if __name__ == "__main__":
    main()
