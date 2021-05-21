#!/usr/bin/env pypy3

MODULUS = 2147483647


def lehmer_rng(m, a, x):
    return (a * x) % m


def part1(a, b):
    result = 0

    for _ in range(40_000_000):
        a = lehmer_rng(MODULUS, 16807, a)
        b = lehmer_rng(MODULUS, 48271, b)
        result += (a & 0xffff) == (b & 0xffff)

    return result


def part2(a, b):
    result = 0

    for _ in range(5_000_000):
        while True:
            a = lehmer_rng(MODULUS, 16807, a)
            if (a % 4) == 0:
                break
        while True:
            b = lehmer_rng(MODULUS, 48271, b)
            if (b % 8) == 0:
                break
        result += (a & 0xffff) == (b & 0xffff)

    return result


def main():
    print(part1(116, 299))
    print(part2(116, 299))


if __name__ == "__main__":
    main()
