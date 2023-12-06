#!/usr/bin/env pypy3

import math

EXPECTED_PART_1 = 288


def transpose(xss):
    return list(zip(*xss))


def read_input(filename):
    with open(filename) as lines:
        times, dists = lines
        return transpose(zip(map(int, times.split()[1:]), map(int, dists.split()[1:])))


def ways_to_beat_distance_record(time, distance):
    return sum(
        1
        for acceleration_time in range(time)
        if (time - acceleration_time) * acceleration_time > distance
    )


def part_1(times, distances):
    return math.prod(
        ways_to_beat_distance_record(time, distance)
        for time, distance in zip(times, distances)
    )


def test_part_1():
    times, distances = read_input("input_test")
    assert part_1(times, distances) == EXPECTED_PART_1


def main():
    times, distances = read_input("input")
    print(part_1(times, distances))


if __name__ == "__main__":
    main()
