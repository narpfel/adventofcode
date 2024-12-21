#!/usr/bin/env python3

from collections import Counter
from itertools import pairwise
from itertools import product

EXPECTED_PART_1 = 126384

NUMERIC_KEYPAD = {
    (0, 0): "7",
    (1, 0): "8",
    (2, 0): "9",
    (0, 1): "4",
    (1, 1): "5",
    (2, 1): "6",
    (0, 2): "1",
    (1, 2): "2",
    (2, 2): "3",
    (1, 3): "0",
    (2, 3): "A",
}

NUMERIC_KEY_POSITION = {key: loc for loc, key in NUMERIC_KEYPAD.items()}

DIRECTIONAL_KEYPAD = {
    (1, 0): "^",
    (2, 0): "A",
    (0, 1): "<",
    (1, 1): "v",
    (2, 1): ">",
}

DIRECTIONAL_KEY_POSITION = {key: loc for loc, key in DIRECTIONAL_KEYPAD.items()}


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def get_moves_for_numeric(start, end):
    x, y = NUMERIC_KEY_POSITION[start]
    X, Y = NUMERIC_KEY_POSITION[end]
    moves = [
        "^" * (y - Y) if start in "0A" else "",
        "<" * (x - X),
        "v" * (Y - y),
        "^" * (y - Y) if start not in "0A" else "",
        ">" * (X - x),
        "A",
    ]
    return "".join(moves)


def get_moves_for_directional(start, end):
    x, y = DIRECTIONAL_KEY_POSITION[start]
    X, Y = DIRECTIONAL_KEY_POSITION[end]
    moves = []

    if end == "<" and y < Y:
        y += 1
        moves.append("v")

    if start == "<":
        moves.append(">" * (X - x))
        moves.append("^" * (y - Y))
    else:
        moves.append("<" * (x - X))
        moves.append("v" * (Y - y))
        moves.append("^" * (y - Y))
        moves.append(">" * (X - x))

    moves.append("A")
    return "".join(moves)


def apply_moves_numeric(moves):
    x, y = NUMERIC_KEY_POSITION["A"]
    output = []
    for move in moves:
        match move:
            case "A":
                output.append(NUMERIC_KEYPAD[x, y])
            case "<":
                x -= 1
            case ">":
                x += 1
            case "^":
                y -= 1
            case "v":
                y += 1
        assert (x, y) in NUMERIC_KEYPAD
    return "".join(output)


def apply_moves_directional(moves):
    x, y = DIRECTIONAL_KEY_POSITION["A"]
    output = []
    for move in moves:
        match move:
            case "A":
                output.append(DIRECTIONAL_KEYPAD[x, y])
            case "<":
                x -= 1
            case ">":
                x += 1
            case "^":
                y -= 1
            case "v":
                y += 1
        assert (x, y) in DIRECTIONAL_KEYPAD
    return "".join(output)


def part_1(codes):
    result = 0
    for code in codes:
        numeric_part = int(code.removesuffix("A"))
        moves = "".join(get_moves_for_numeric(start, end) for start, end in pairwise("A" + code))
        for _ in range(2):
            moves = "".join(
                get_moves_for_directional(start, end)
                for start, end in pairwise("A" + moves)
            )
        assert apply_moves_numeric(apply_moves_directional(apply_moves_directional(moves))) == code
        result += numeric_part * len(moves)
    return result


DIRECTIONAL_KEYPAD_MOVES = {
    (start, end): list(pairwise("A" + get_moves_for_directional(start, end)))
    for start, end in product(DIRECTIONAL_KEY_POSITION, repeat=2)
}


def count_directional_moves(moves):
    move_counts = Counter()
    for move, count in moves.items():
        for move in DIRECTIONAL_KEYPAD_MOVES[move]:
            move_counts[move] += count
    return move_counts


def part_2(codes, directional_keyboard_count=26):
    result = 0
    for code in codes:
        numeric_part = int(code.removesuffix("A"))
        moves = "".join(get_moves_for_numeric(start, end) for start, end in pairwise("A" + code))
        moves = Counter(pairwise("A" + moves))
        for _ in range(directional_keyboard_count - 1):
            moves = count_directional_moves(moves)
        result += numeric_part * moves.total()
    return result


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input, directional_keyboard_count=3) == EXPECTED_PART_1


def main():
    codes = read_input("input")
    print(part_1(codes))
    print(part_2(codes))


if __name__ == "__main__":
    main()
