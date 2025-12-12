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
    # rough manual approximation of how the shapes can be packed semi-efficiently:
    #
    # 540: 3 shapes in 3x6 => 6 tiles per shape
    # ###
    # ###
    # ###
    # ###
    # ###
    # ###
    #
    # 223: 3 shapes in 4x6 => 8 tiles per shape
    # .###
    # ######
    # #####
    # ######
    #
    # shape 1 is approximated with 8 tiles needed

    average_space_needed = [6, 8, 8, 8, 6, 6]
    return sum(
        x * y >= sum(avg * amount for avg, amount in zip(average_space_needed, amounts))
        for (x, y), amounts in regions
    )


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
