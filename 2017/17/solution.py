#!/usr/bin/env pypy3


INPUT = 337


def part1(n):
    xs = []
    i = 0
    for x in range(2018):
        xs.insert(i + 1, x)
        i = (i + n + 1) % (x + 1)
    return xs[(xs.index(2017) + 1) % len(xs)]


def part2(n):
    i = 0
    for x in range(50000000):
        if i == 0:
            result = x
        i = (i + n + 1) % (x + 1)
    return result


def main():
    print(part1(INPUT))
    print(part2(INPUT))


if __name__ == "__main__":
    main()
