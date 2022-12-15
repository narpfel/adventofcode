#!/usr/bin/env python3

import re

EXPECTED_PART_1 = 26

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
    blocked = set()
    for (sx, sy), (bx, by) in coords:
        sensor_range = abs(sx - bx) + abs(sy - by)
        line_length = (sensor_range - abs(target_y - sy)) * 2 + 1
        if line_length > 0:
            blocked.update(range(sx - line_length // 2, sx + line_length // 2 + 1))
    return blocked


def part_1(coords, target_y):
    blocked = blocked_in_line(coords, target_y)
    beacons_in_blocked = {x for _, (x, y) in coords if y == target_y and x in blocked}
    return len(blocked) - len(beacons_in_blocked)


def test_part_1():
    puzzle_input = list(read_input("input_test"))
    assert part_1(puzzle_input, 10) == EXPECTED_PART_1


def main():
    coords = list(read_input("input"))
    print(part_1(coords, 2_000_000))


if __name__ == "__main__":
    main()
