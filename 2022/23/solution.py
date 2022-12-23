#!/usr/bin/env pypy3

from collections import Counter
from collections import deque

EXPECTED_PART_1 = 110


def north(x, y):
    return x, y - 1


def northeast(x, y):
    return x + 1, y - 1


def east(x, y):
    return x + 1, y


def southeast(x, y):
    return x + 1, y + 1


def south(x, y):
    return x, y + 1


def southwest(x, y):
    return x - 1, y + 1


def west(x, y):
    return x - 1, y


def northwest(x, y):
    return x - 1, y - 1


DIRECTIONS = [
    ((northeast, north, northwest), north),
    ((southeast, south, southwest), south),
    ((northwest, west, southwest), west),
    ((northeast, east, southeast), east),
]


def neighbours(x, y):
    return [
        north(x, y),
        northeast(x, y),
        east(x, y),
        southeast(x, y),
        south(x, y),
        southwest(x, y),
        west(x, y),
        northwest(x, y),
    ]


def read_input(filename):
    with open(filename) as lines:
        return frozenset(
            (x, y)
            for y, line in enumerate(lines)
            for x, c in enumerate(line)
            if c == "#"
        )


def step(grove, directions):
    proposals = {}
    not_moved = set()

    for x, y in grove:
        neighbour_count = sum(neighbour in grove for neighbour in neighbours(x, y))
        if neighbour_count != 0:
            for look_directions, move_direction in directions:
                if all(direction(x, y) not in grove for direction in look_directions):
                    proposals[x, y] = move_direction(x, y)
                    break
            else:
                not_moved.add((x, y))
        else:
            not_moved.add((x, y))

    proposal_counts = Counter(proposals.values())
    grove = set()

    for elf, proposal in proposals.items():
        if proposal_counts[proposal] == 1:
            grove.add(proposal)
        else:
            grove.add(elf)

    grove |= not_moved
    directions.rotate(-1)

    return grove


def part_1(grove):
    directions = deque(DIRECTIONS)
    for _ in range(10):
        grove = step(grove, directions)

    min_x = min(x for x, _ in grove)
    max_x = max(x for x, _ in grove)
    min_y = min(y for _, y in grove)
    max_y = max(y for _, y in grove)
    return (max_x - min_x + 1) * (max_y - min_y + 1) - len(grove)


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def main():
    grove = read_input("input")
    print(part_1(grove))


if __name__ == "__main__":
    main()
