#!/usr/bin/env python3
from collections import namedtuple


class Position(namedtuple("Position", "x, y")):
    def transpose(self):
        return Position(self.y, self.x)


def find_starting_column(by_line):
    return by_line[0].index("|")


def transpose(xs):
    return ("".join(row) for row in zip(*xs))


def nonnegative(x):
    return x >= 0


def next_direction(by_line, position):
    if by_line[position.y - 1][position.x] == " ":
        return go_down
    else:
        return go_up


def transpose_direction(direction):
    if direction == go_up:
        return go_left
    else:
        return go_right


def go_left(by_line, _, position):
    line = by_line[position.y]
    begin = max(
        filter(
            nonnegative,
            [line.rfind("+", 0, position.x - 1), line.rfind(" ", 0, position.x - 1) + 1],
        ),
    )
    steps = line[begin:position.x]
    position = position._replace(x=position.x - len(steps))
    return steps[::-1], position, next_direction(by_line, position)


def go_right(by_line, _, position):
    line = by_line[position.y]
    end = min(
        filter(
            nonnegative,
            [line.find("+", position.x + 1), line.find(" ", position.x + 1)],
        ),
    )
    steps = line[position.x:end]
    position = position._replace(x=position.x + len(steps))
    return steps, position, next_direction(by_line, position)


def go_up(_, by_column, position):
    steps, position, direction = go_left(by_column, None, position.transpose())
    return steps, position.transpose(), transpose_direction(direction)


def go_down(_, by_column, position):
    steps, position, direction = go_right(by_column, None, position.transpose())
    return steps, position.transpose(), transpose_direction(direction)


def go(by_line, by_column, position, direction):
    while True:
        steps, position, direction = direction(by_line, by_column, position)
        yield from steps
        if by_column[position.x][position.y] != "+":
            return


def main():
    with open("input") as lines:
        by_line = [line[:-1] for line in lines if line.strip()]
    by_column = list(transpose(by_line))
    path = list(go(by_line, by_column, Position(find_starting_column(by_line), 0), go_down))
    print("".join(filter(str.isalpha, path)))
    print(1 + len(path))


if __name__ == "__main__":
    main()
