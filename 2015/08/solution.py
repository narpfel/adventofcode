#!/usr/bin/env python3

from ast import literal_eval


def main():
    repr_length = 0
    length = 0
    repr_repr_length = 0
    with open("input") as lines:
        for line in lines:
            repr_length += len(line.strip())
            length += len(literal_eval(line.strip()))
            repr_repr_length += len(line.strip().replace("\\", "\\\\").replace('"', '\\"')) + 2

    print(repr_length - length)
    print(repr_repr_length - repr_length)


if __name__ == '__main__':
    main()
