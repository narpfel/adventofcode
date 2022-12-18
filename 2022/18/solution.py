#!/usr/bin/env python3

from collections import Counter

EXPECTED_PART_1 = 64


def read_input(filename):
    with open(filename) as lines:
        return [tuple(int(s) for s in line.split(",")) for line in lines]


def cube_faces(cube):
    x, y, z = cube
    x *= 2
    y *= 2
    z *= 2
    return {
        (x - 1, y, z),
        (x + 1, y, z),
        (x, y - 1, z),
        (x, y + 1, z),
        (x, y, z - 1),
        (x, y, z + 1),
    }


def part_1(cubes):
    faces = Counter()

    for cube in cubes:
        faces.update(cube_faces(cube))

    return sum(count == 1 for count in faces.values())


def test_simple():
    assert part_1([(2, 1, 1), (1, 1, 1)]) == 10


def test_part_1():
    cubes = read_input("input_test")
    assert part_1(cubes) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
