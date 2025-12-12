#!/usr/bin/env python3

def read_input(filename):
    with open(filename) as lines:
        regions = lines.read().split("\n\n")[-1]
        for line in regions.splitlines():
            size, _, amounts = line.partition(": ")
            x, y = map(int, size.split("x"))
            amounts = [int(amount) for amount in amounts.split()]
            yield (x, y), amounts


def part_1(regions):
    return sum(x * y >= 9 * sum(amounts) for (x, y), amounts in regions)


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
