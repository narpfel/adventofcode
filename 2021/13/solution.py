#!/usr/bin/env python3

import re

import numpy as np

FOLD_RE = re.compile(r"fold along (?P<axis>.)=(?P<coord>\d+)")


def fold_x(paper, x):
    return fold_y(paper.T, x).T


def fold_y(paper, y):
    upper = paper[:y, :]
    lower = paper[y + 1:, :]
    return upper | lower[::-1]


FOLDS = {"x": fold_x, "y": fold_y}


def print_paper(paper):
    for line in paper:
        print("".join("\u2588" if cell else " " for cell in line))


def apply_folds(paper, folds):
    for axis, coord in folds:
        paper = FOLDS[axis](paper, coord)
    return paper


def main():
    with open("input") as file:
        dots, folds = file.read().split("\n\n")
        dots = [(int(x), int(y)) for x, y in (line.split(",") for line in dots.splitlines())]
        folds = [(m["axis"], int(m["coord"])) for m in map(FOLD_RE.match, folds.splitlines())]

    paper = np.zeros((max(y for _, y in dots) + 1, max(x for x, _ in dots) + 1), dtype=bool)
    for x, y in dots:
        paper[y, x] = True

    print(apply_folds(paper, folds[:1]).sum())
    print_paper(apply_folds(paper, folds))


if __name__ == "__main__":
    main()
