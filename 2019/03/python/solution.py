#!/usr/bin/env python3

from itertools import count


def move(point, direction):
    x, y = point
    if direction == "R":
        x += 1
    elif direction == "L":
        x -= 1
    elif direction == "U":
        y += 1
    elif direction == "D":
        y -= 1
    return x, y


def manhattan_distance(point):
    return abs(point[0]) + abs(point[1])


def track(steps):
    position = (0, 0)
    index = count(1)
    for (direction, length) in steps:
        for _ in range(length):
            position = move(position, direction)
            yield position, (manhattan_distance(position), next(index))


def parse(s):
    return s[0], int(s[1:])


def main():
    with open("input") as lines:
        tracks = [dict(track(parse(s) for s in line.split(","))) for line in lines]
    crossings = tracks[0].keys() & tracks[1].keys()
    print(min(tracks[0][crossing][0] for crossing in crossings))
    print(
        min(tracks[0][crossing][1] + tracks[1][crossing][1] for crossing in crossings),
    )


if __name__ == "__main__":
    main()
