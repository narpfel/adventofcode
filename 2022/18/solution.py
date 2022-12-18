#!/usr/bin/env python3

from collections import Counter

EXPECTED_PART_1 = 64
EXPECTED_PART_2 = 58


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


def neighbours(cube):
    x, y, z = cube
    return [
        (x - 1, y, z),
        (x + 1, y, z),
        (x, y - 1, z),
        (x, y + 1, z),
        (x, y, z - 1),
        (x, y, z + 1),
    ]


def part_2(cubes):
    cubes = set(cubes)

    min_x = min(cube[0] for cube in cubes) - 2
    max_x = max(cube[0] for cube in cubes) + 3
    min_y = min(cube[1] for cube in cubes) - 2
    max_y = max(cube[1] for cube in cubes) + 3
    min_z = min(cube[2] for cube in cubes) - 2
    max_z = max(cube[2] for cube in cubes) + 3
    x_range = range(min_x, max_x)
    y_range = range(min_y, max_y)
    z_range = range(min_z, max_z)

    # floodfill cuboid containing all small cubes
    seen = set()
    next_points = [(min_x, min_y, min_z)]

    while next_points:
        cube = next_points.pop()
        if cube not in seen:
            seen.add(cube)
            for neighbour in neighbours(cube):
                x, y, z = neighbour
                if x in x_range and y in y_range and z in z_range and neighbour not in cubes:
                    next_points.append(neighbour)

    length = max_x - min_x
    width = max_y - min_y
    height = max_z - min_z

    cubes_area = part_1(cubes)
    interior_area_plus_surrounding_cuboid_area = part_1(cubes | seen)
    surrounding_cuboid_area = 2 * (length * width + length * height + width * height)

    return cubes_area - (interior_area_plus_surrounding_cuboid_area - surrounding_cuboid_area)


def test_simple():
    assert part_1([(2, 1, 1), (1, 1, 1)]) == 10


def test_part_1():
    cubes = read_input("input_test")
    assert part_1(cubes) == EXPECTED_PART_1


def test_part_2():
    cubes = read_input("input_test")
    assert part_2(cubes) == EXPECTED_PART_2


def main():
    cubes = read_input("input")
    print(part_1(cubes))
    print(part_2(cubes))


if __name__ == "__main__":
    main()
