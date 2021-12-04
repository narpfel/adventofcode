#!/usr/bin/env python3

from itertools import chain
from pathlib import Path


def parse_board(lines):
    return [
        [[int(n), False] for n in line.split()]
        for line in lines.splitlines()
    ]


def compute_score(board):
    for line in chain(board, zip(*board)):
        if all(checked for _, checked in line):
            return sum(
                sum(number for number, checked in line if not checked)
                for line in board
            )
    return None


def main():
    numbers, *boards = Path("input").read_text().split("\n\n")
    numbers = list(map(int, numbers.split(",")))
    boards = list(map(parse_board, boards))

    solutions = []

    for number in numbers:
        for board in boards:
            for line in board:
                for cell in line:
                    if cell[0] == number:
                        cell[1] = True

        for board in boards:
            maybe_score = compute_score(board)
            if maybe_score is not None:
                solutions.append(maybe_score * number)
                boards.remove(board)

    print(solutions[0])
    print(solutions[-1])


if __name__ == "__main__":
    main()
