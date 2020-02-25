#!/usr/bin/env python3

from bisect import bisect
from collections import defaultdict
from functools import partial
from math import ceil

from pytest import mark


ONE_TRILLION = 10 ** 12


def batch_count(amount, batchsize):
    return ceil(amount / batchsize)


def read_input(filename):
    with open(filename) as lines:
        return parse_reactions(lines)


def parse_reactions(lines):
    reactions = {}
    for line in lines:
        educts, _, product = line.partition(" => ")
        amount, product = product.split()
        amount = int(amount)
        educts = (educt.split() for educt in educts.split(", "))
        reactions[product] = amount, {educt: int(amount) for (amount, educt) in educts}
    return reactions


def solve(reactions, target_amount):
    stuff = defaultdict(int, {"FUEL": target_amount})
    overproduced = defaultdict(int)

    while set(stuff) != {"ORE"}:
        product = next(filter(lambda k: k != "ORE", stuff.keys()))
        amount = stuff.pop(product)
        batchsize, educts = reactions[product]

        if overproduced[product] >= amount:
            overproduced[product] -= amount
            continue
        else:
            amount -= overproduced.pop(product, 0)

        batches = batch_count(amount, batchsize)
        overproduced[product] += batches * batchsize - amount

        for educt, amount_needed_per_batch in educts.items():
            stuff[educt] = stuff.pop(educt, 0) + batches * amount_needed_per_batch

    return stuff["ORE"]


class FakeContainer:
    def __init__(self, f):
        self.f = f

    def __getitem__(self, index):
        return self.f(index)


def part1(reactions):
    return solve(reactions, 1)


def part2(reactions):
    return bisect(FakeContainer(partial(solve, reactions)), ONE_TRILLION, 0, ONE_TRILLION) - 1


@mark.parametrize(
    "number, expected",
    [(0, 165), (1, 13312), (2, 180697), (3, 2210736)]
)
def test_part1(number, expected):
    assert part1(read_input(f"input_test{number}")) == expected


@mark.parametrize(
    "number, expected",
    [(1, 82892753), (2, 5586022), (3, 460664)]
)
def test_part2(number, expected):
    assert part2(read_input(f"input_test{number}")) == expected


def main():
    reactions = read_input("input")
    print(part1(reactions))
    print(part2(reactions))


if __name__ == "__main__":
    main()
