#!/usr/bin/env python3

from collections import Counter
from itertools import pairwise
from itertools import product

EXPECTED_PART_1 = 126384

NUMERIC_KEYPAD = {
    "7": (0, 0),
    "8": (1, 0),
    "9": (2, 0),
    "4": (0, 1),
    "5": (1, 1),
    "6": (2, 1),
    "1": (0, 2),
    "2": (1, 2),
    "3": (2, 2),
    "0": (1, 3),
    "A": (2, 3),
}

DIRECTIONAL_KEYPAD = {
    "^": (1, 0),
    "A": (2, 0),
    "<": (0, 1),
    "v": (1, 1),
    ">": (2, 1),
}


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def get_moves_for_numeric(start, end):
    x, y = NUMERIC_KEYPAD[start]
    X, Y = NUMERIC_KEYPAD[end]
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
    x, y = DIRECTIONAL_KEYPAD[start]
    X, Y = DIRECTIONAL_KEYPAD[end]
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


DIRECTIONAL_KEYPAD_MOVES = {
    (start, end): list(pairwise("A" + get_moves_for_directional(start, end)))
    for start, end in product(DIRECTIONAL_KEYPAD, repeat=2)
}


def count_directional_moves(moves):
    move_counts = Counter()
    for move, count in moves.items():
        for move in DIRECTIONAL_KEYPAD_MOVES[move]:
            move_counts[move] += count
    return move_counts


def solve(codes, *, directional_keyboard_count):
    result = 0
    for code in codes:
        numeric_part = int(code.removesuffix("A"))
        moves = "".join(get_moves_for_numeric(start, end) for start, end in pairwise("A" + code))
        moves = Counter(pairwise("A" + moves))
        for _ in range(directional_keyboard_count - 1):
            moves = count_directional_moves(moves)
        result += numeric_part * moves.total()
    return result


def part_1(codes):
    return solve(codes, directional_keyboard_count=3)


def part_2(codes):
    return solve(codes, directional_keyboard_count=26)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    codes = read_input("input")
    print(part_1(codes))
    print(part_2(codes))


if __name__ == "__main__":
    main()
