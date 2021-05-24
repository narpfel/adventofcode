#!/usr/bin/env pypy3

INPUT = "16,12,1,0,15,7,11"


def parse_input(starting_numbers):
    return [int(n) for n in starting_numbers.split(",")]


def solve(starting_numbers, turn_count):
    number_to_turn = [-1] * turn_count
    for i, n in enumerate(starting_numbers[:-1]):
        number_to_turn[n] = i
    last_spoken = starting_numbers[-1]

    # nice PyPy feature: range() lists don’t create the whole list in memory
    for turn in range(len(starting_numbers), turn_count):
        last_spoken_on_turn = number_to_turn[last_spoken]
        number_to_turn[last_spoken] = turn - 1
        if last_spoken_on_turn < 0:
            last_spoken = 0
        else:
            last_spoken = turn - last_spoken_on_turn - 1

    return last_spoken


def main():
    print(solve(parse_input(INPUT), 2020))
    print(solve(parse_input(INPUT), 30 * 10**6))


def rpython_main(argv):
    main()
    return 0


def target(*args):
    return rpython_main


if __name__ == "__main__":
    main()
