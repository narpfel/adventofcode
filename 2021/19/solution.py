#!/usr/bin/env python3

from collections import Counter
from collections import defaultdict
from itertools import combinations
from itertools import product

import numpy as np
from scipy.spatial.transform import Rotation

ROTATIONS = [
    Rotation.from_matrix(np.array(rotation).reshape((3, 3)))
    for rotation in {
        tuple(rotation.flatten())
        for rotation in [
            np.rint(rotation.as_matrix()).astype(int)
            for rotation in [
                Rotation.from_euler("xyz", [90 * x, 90 * y, 90 * z], degrees=True)
                for x, y, z in product(range(4), repeat=3)
            ]
        ]
    }
]


def rotate(points, rotation):
    return np.rint(rotation.apply(points.reshape((-1, 3)))).astype(int).reshape(points.shape)


def parse_scanner(block):
    return np.array([
        [int(s) for s in line.split(",")]
        for line in block.splitlines()[1:]
    ])


def read_from_file(filename):
    with open(filename) as file:
        return [parse_scanner(block.strip()) for block in file.read().split("\n\n")]


def find_relative_scanner_orientations(scanners):
    for (i, x), (j, y) in product(enumerate(scanners), repeat=2):
        if i == j:
            continue
        for rotation in ROTATIONS:
            for translation, overlap in Counter(
                tuple(p1 - p2)
                for p1, p2 in product(x, rotate(y, rotation))
            ).items():
                if overlap >= 12:
                    yield i, j, rotation, translation


def find_beacon_positions(scanners, seen, relative_scanner_orientations, start):
    all_beacons = set(map(tuple, scanners[start]))
    for j, [(rotation, translation)] in relative_scanner_orientations[start].items():
        if j not in seen:
            seen.add(j)
            new_points = np.array(
                list(
                    find_beacon_positions(scanners, seen, relative_scanner_orientations, j),
                ),
            )
            new_points = rotate(new_points, rotation)
            new_points += translation
            all_beacons.update(map(tuple, new_points))
    return all_beacons


def find_scanner_positions(scanners, seen, relative_scanner_orientations, start):
    scanner_positions = [(0, 0, 0)]
    for j, [(rotation, translation)] in relative_scanner_orientations[start].items():
        if j not in seen:
            seen.add(j)
            new_positions = np.array(
                find_scanner_positions(scanners, seen, relative_scanner_orientations, j),
            )
            new_positions = rotate(new_positions, rotation)
            new_positions += translation
            scanner_positions.extend(map(tuple, new_positions))
    return scanner_positions


def distance(p1, p2):
    return sum(abs(x1 - x2) for x1, x2 in zip(p1, p2, strict=True))


def main():
    scanners = read_from_file("input")
    relative_scanner_orientations = defaultdict(lambda: defaultdict(list))
    for i, j, rotation, translation in find_relative_scanner_orientations(scanners):
        relative_scanner_orientations[i][j].append((rotation, translation))

    assert len(relative_scanner_orientations) == len(scanners)
    all_beacons = find_beacon_positions(scanners, {0}, relative_scanner_orientations, 0)
    print(len(all_beacons))
    scanner_positions = find_scanner_positions(scanners, {0}, relative_scanner_orientations, 0)
    print(max(distance(x, y) for x, y in combinations(scanner_positions, r=2)))


if __name__ == "__main__":
    main()
