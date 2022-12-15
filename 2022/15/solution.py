#!/usr/bin/env pypy3

import re
import sys

sys.path.insert(0, "../../2016")
sparse = __import__("20.solution").solution

EXPECTED_PART_1 = 26
EXPECTED_PART_2 = 56000011

SENSOR_RE = re.compile(
    r"Sensor at x=(?P<sensor_x>-?\d+), y=(?P<sensor_y>-?\d+): "
    r"closest beacon is at x=(?P<beacon_x>-?\d+), y=(?P<beacon_y>-?\d+)",
)


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            match = SENSOR_RE.match(line)
            assert match is not None
            yield (
                (int(match["sensor_x"]), int(match["sensor_y"])),
                (int(match["beacon_x"]), int(match["beacon_y"])),
            )


def blocked_in_line(coords, target_y):
    blocked = []
    for (sx, sy), (bx, by) in coords:
        sensor_range = abs(sx - bx) + abs(sy - by)
        distance = abs(target_y - sy)
        if distance <= sensor_range:
            line_length = (sensor_range - distance) * 2 + 1
            sparse.insert(blocked, (sx - line_length // 2, sx + line_length // 2))
    return blocked


def part_1(coords, target_y):
    blocked = list(sparse.compactify(blocked_in_line(coords, target_y)))
    blocked_position_count = sparse.length(blocked)
    beacons_in_blocked = {
        x
        for _, (x, y) in coords
        if y == target_y and sparse.contains(blocked, x)
    }
    return blocked_position_count - len(beacons_in_blocked)


def part_2(coords, max_y):
    coords = list(coords)
    for y in range(max_y):
        blocked = blocked_in_line(coords, y)
        if (len(blocked) // 2) % 2 == 0:
            blocked = list(sparse.compactify(blocked))
            x = blocked[1] + 1
            return x * 4_000_000 + y


def test_part_1():
    puzzle_input = list(read_input("input_test"))
    assert part_1(puzzle_input, 10) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input, 20) == EXPECTED_PART_2


def main():
    coords = list(read_input("input"))
    print(part_1(coords, 2_000_000))
    print(part_2(coords, 4_000_000))


if __name__ == "__main__":
    main()
