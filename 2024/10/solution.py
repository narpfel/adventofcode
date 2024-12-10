#!/usr/bin/env python3

EXPECTED_PART_1 = 36


def read_input(filename):
    with open(filename) as lines:
        height_map = {
            (x, y): 100 if c == "." else int(c)
            for y, line in enumerate(lines)
            for x, c in enumerate(line.strip())
        }

    zeros = [(x, y) for (x, y), height in height_map.items() if height == 0]
    return height_map, zeros


def neighbours(x, y):
    yield x - 1, y
    yield x + 1, y
    yield x, y - 1
    yield x, y + 1


def find_path(x, y, height_map, height):
    if height == 9:
        yield (x, y)
    else:
        for nx, ny in neighbours(x, y):
            if height_map.get((nx, ny)) == height + 1:
                yield from find_path(nx, ny, height_map, height + 1)


def part_1(puzzle_input):
    height_map, zeros = puzzle_input
    return sum(len(set(find_path(x, y, height_map, 0))) for x, y in zeros)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
