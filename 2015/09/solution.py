#!/usr/bin/env python3

import re
from collections import defaultdict
from itertools import tee


DISTANCE_SPEC = re.compile(r"(?P<start>\w*) to (?P<end>\w*) = (?P<distance>\d*)")


def iter_paths(connections, excluded=None):
    if excluded is None:
        excluded = set()
    remaining_edges = connections.keys() - excluded

    if len(remaining_edges) == 1:
        yield list(remaining_edges)
        return

    for start in remaining_edges:
        for end in iter_paths(connections, excluded | {start}):
            yield [start, *end]


def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)


def pathlen(path, distances):
    distance = 0
    for start, end in pairwise(path):
        distance += distances[start][end]
    return distance


def main():
    distances = defaultdict(dict)
    with open("input") as lines:
        for line in lines:
            start, end, distance = DISTANCE_SPEC.match(line).groups()
            distances[start][end] = int(distance)
            distances[end][start] = int(distance)

    pathlens = [pathlen(path, distances) for path in iter_paths(distances)]

    print(min(pathlens))
    print(max(pathlens))


if __name__ == '__main__':
    main()
