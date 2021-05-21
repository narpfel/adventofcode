#!/usr/bin/env pypy3
from functools import partial
from itertools import islice

MODULUS = 2147483647


def lehmer_rng(m, a, x):
    return (a * x) % m


def generator(a, x):
    while True:
        x = lehmer_rng(MODULUS, a, x)
        yield x


# manually inline `zip` and `filter` for a 10x performance increase
def zipfilter(xs, xpred, ys, ypred):
    xs = iter(xs)
    ys = iter(ys)
    while True:
        for x in xs:
            if xpred(x):
                break
        for y in ys:
            if ypred(y):
                break
        yield x, y


def solve(length, a, pa, b, pb):
    return sum(
        (x & 0xffff) == (y & 0xffff)
        for (x, y) in islice(
            zipfilter(generator(16807, a), pa, generator(48271, b), pb),
            length,
        )
    )


def part1(a, b):
    return solve(40_000_000, a, lambda _: True, b, lambda _: True)


def is_multiple_of(a, b):
    return (b % a) == 0


def part2(a, b):
    return solve(5_000_000, a, partial(is_multiple_of, 4), b, partial(is_multiple_of, 8))


def main():
    print(part1(116, 299))
    print(part2(116, 299))


if __name__ == "__main__":
    main()
