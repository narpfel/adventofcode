#!/usr/bin/env python3

from string import ascii_letters


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


if __name__ == "__main__":
    main()
