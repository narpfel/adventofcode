#!/usr/bin/env python3

from itertools import combinations

import z3

EXPECTED_PART_1 = 2
EXPECTED_PART_2 = 47


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            p, v = line.split(" @ ")
            yield list(map(int, p.split(", "))), list(map(int, v.split(", ")))


def cross_xy(h1, h2):
    (p1x, p1y, _), (v1x, v1y, _) = h1
    (p2x, p2y, _), (v2x, v2y, _) = h2

    denominator = v1x * v2y - v1y * v2x

    if denominator == 0:
        return None

    t = ((p1x - p2x) * (-v2y) - (p1y - p2y) * (-v2x)) / denominator
    u = ((p1x - p2x) * (-v1y) - (p1y - p2y) * (-v1x)) / denominator

    if t < 0 or u < 0:
        return None
    else:
        return (p1x + t * v1x, p1y + t * v1y)


def crosses_xy_in_range(check_range, h1, h2):
    crossing_point = cross_xy(h1, h2)
    if crossing_point is None:
        return False
    else:
        x, y = crossing_point
        return (
            (check_range.start <= x <= check_range.stop)
            and (check_range.start <= y <= check_range.stop)
        )


def part_1(hail, check_range=range(200000000000000, 400000000000000)):
    return sum(
        crosses_xy_in_range(check_range, h1, h2)
        for h1, h2 in combinations(hail, r=2)
    )


def part_2(hail):
    solver = z3.Solver()

    rx, ry, rz = z3.Int("rx"), z3.Int("ry"), z3.Int("rz")
    rvx, rvy, rvz = z3.Int("rvx"), z3.Int("rvy"), z3.Int("rvz")

    for name, ((x, y, z), (vx, vy, vz)) in enumerate(hail):
        t = z3.Int(f"t{name}")
        solver.add(x + t * vx == rx + t * rvx)
        solver.add(y + t * vy == ry + t * rvy)
        solver.add(z + t * vz == rz + t * rvz)

    assert solver.check() == z3.sat
    model = solver.model()
    return model[rx].as_long() + model[ry].as_long() + model[rz].as_long()


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input, check_range=range(7, 27)) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    hail = list(read_input("input"))
    print(part_1(hail))
    print(part_2(hail))


if __name__ == "__main__":
    main()
