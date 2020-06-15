#!/usr/bin/env python3
from collections import defaultdict
from itertools import count
from itertools import islice

INPUT = 265149


def iter_manhatten_distances():
    yield 0
    for layer in count(1):
        for _ in range(4):
            yield from reversed(range(layer, 2 * layer))
            yield from range(layer + 1, 2 * layer + 1)


def iter_positions():
    yield (0, 0)
    for layer in count(1):
        yield from iter_layer_positions(layer)


def iter_layer_positions(layer):
    for y in range(-layer + 1, layer + 1):
        yield (layer, y)
    for x in reversed(range(-layer, layer)):
        yield (x, layer)
    for y in reversed(range(-layer, layer)):
        yield (-layer, y)
    for x in range(-layer + 1, layer + 1):
        yield (x, -layer)


def adjacent_positions(position):
    x, y = position
    return [
        (x - 1, y - 1), (x - 1, y), (x - 1, y + 1),
        (x, y - 1), (x, y + 1),
        (x + 1, y - 1), (x + 1, y), (x + 1, y + 1),
    ]


def main():
    print(next(islice(iter_manhatten_distances(), INPUT - 1, None)))

    memory = defaultdict(int)
    memory[(0, 0)] = 1

    for position in islice(iter_positions(), 1, None):
        memory[position] = sum(
            memory[p]
            for p in adjacent_positions(position)
        )
        if memory[position] > INPUT:
            print(memory[position])
            break


if __name__ == '__main__':
    main()
