#!/usr/bin/env python3

from string import ascii_letters

from more_itertools import chunked


def main():
    with open("input") as input_file:
        rucksacks = [line.strip() for line in input_file]

    print(
        sum(
            sum(
                ascii_letters.index(c) + 1
                for c in set(rucksack[len(rucksack) // 2:]) & set(rucksack[:len(rucksack) // 2])
            )
            for rucksack in rucksacks
        ),
    )
    print(
        sum(
            sum(
                ascii_letters.index(c) + 1
                for c in set(group[0]).intersection(*group[1:])
            )
            for group in chunked(rucksacks, 3)
        ),
    )


if __name__ == "__main__":
    main()
