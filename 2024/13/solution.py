#!/usr/bin/env python3

import re

import z3

EXPECTED_PART_1 = 480

NUMBER_RE = re.compile(r"\d+")

A_LOT = 10000000000000


def read_input(filename):
    with open(filename) as lines:
        for chunk in lines.read().split("\n\n"):
            ax, ay, bx, by, px, py = NUMBER_RE.findall(chunk)
            yield (
                (int(ax), int(ay)),
                (int(bx), int(by)),
                (int(px), int(py)),
            )


def part_1(machines):
    return sum(
        min(
            (
                3 * n + m
                for n in range(101)
                for m in range(101)
                if n * ax + m * bx == px and n * ay + m * by == py
            ),
            default=0,
        )
        for (ax, ay), (bx, by), (px, py) in machines
    )


def model_machine(machine):
    n = z3.Int("n")
    m = z3.Int("m")
    (ax, ay), (bx, by), (px, py) = machine
    opt = z3.Optimize()
    opt.add(n * ax + m * bx == A_LOT + px)
    opt.add(n * ay + m * by == A_LOT + py)
    opt.minimize(3 * n + m)
    if opt.check() == z3.sat:
        model = opt.model()
        return 3 * model[n].as_long() + model[m].as_long()
    else:
        return None


def part_2(machines):
    return sum(filter(None, map(model_machine, machines)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))
    print(part_2(read_input("input")))


if __name__ == "__main__":
    main()
