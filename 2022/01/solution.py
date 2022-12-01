#!/usr/bin/env python3

def main():
    with open("input") as input_file:
        calories_per_elf = [
            sum(map(int, calories.splitlines()))
            for calories in input_file.read().split("\n\n")
        ]

    print(max(calories_per_elf))
    print(sum(sorted(calories_per_elf)[-3:]))


if __name__ == "__main__":
    main()
