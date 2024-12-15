#!/usr/bin/env python3

EXPECTED_PART_1 = 10092


def read_input(filename):
    with open(filename) as lines:
        warehouse, moves = lines.read().split("\n\n")

    tiles = {}
    for y, line in enumerate(warehouse.splitlines()):
        for x, c in enumerate(line.strip()):
            tiles[x, y] = c

    return tiles, [move for move in moves if move in "<>^v"]


def step(point, move):
    x, y = point
    match move:
        case "^":
            return x, y - 1
        case ">":
            return x + 1, y
        case "v":
            return x, y + 1
        case "<":
            return x - 1, y
        case _:
            raise AssertionError(f"unreachable move: {move!r}")


def part_1(puzzle_input):
    tiles, moves = puzzle_input
    tiles = dict(tiles)
    x, y = next(p for p, tile in tiles.items() if tile == "@")

    for move in moves:
        position = move_target = step((x, y), move)
        while True:
            match tiles[position]:
                case "#":
                    break
                case ".":
                    tiles[x, y] = "."
                    tiles[position] = "O"
                    tiles[move_target] = "@"
                    x, y = move_target
                    break
                case "O":
                    position = step(position, move)

    return sum(
        100 * y + x
        for (x, y), tile in tiles.items()
        if tile == "O"
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1
    puzzle_input = read_input("input_test_2")
    assert part_1(puzzle_input) == 2028


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
