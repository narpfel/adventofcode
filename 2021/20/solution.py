#!/usr/bin/env pypy3

from itertools import cycle
from itertools import islice
from itertools import product


def enhance_step(image, algorithm, rest):
    min_x = min(x for x, _ in image)
    min_y = min(y for _, y in image)
    max_x = max(x for x, _ in image)
    max_y = max(y for _, y in image)

    new_image = {}
    for x, y in product(range(min_x - 1, max_x + 2), range(min_y - 1, max_y + 2)):
        idx = 0
        for dy, dx in product(range(-1, 2), repeat=2):
            idx <<= 1
            idx |= image.get((x + dx, y + dy), rest)
        new_image[(x, y)] = algorithm[idx]

    return new_image


def enhance(image, algorithm, steps):
    for rest in islice(cycle([False, algorithm[0]]), steps):
        image = enhance_step(image, algorithm, rest)

    return image


def main():
    with open("input") as file:
        algorithm, image = file.read().strip().split("\n\n")

    algorithm = [cell == "#" for cell in algorithm.strip()]

    if algorithm[0] == "#" and algorithm[-1] == "#":
        raise AssertionError("there will be infinitely many lit pixels")

    image = {
        (x, y): cell == "#"
        for y, line in enumerate(image.splitlines())
        for x, cell in enumerate(line.strip())
    }

    for steps in [2, 50]:
        print(sum(enhance(image, algorithm, steps).values()))


if __name__ == "__main__":
    main()
