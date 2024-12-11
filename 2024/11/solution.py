#!/usr/bin/env python3

from functools import cache

EXPECTED_PART_1 = 55312


def read_input(filename):
    with open(filename) as lines:
        return [int(number) for number in lines.read().split()]


@cache
def blink(stone, n):
    if n == 0:
        return 1
    elif stone == 0:
        return blink(1, n - 1)
    else:
        s = str(stone)
        if len(s) % 2 == 0:
            return blink(int(s[:len(s) // 2]), n - 1) + blink(int(s[len(s) // 2:]), n - 1)
        else:
            return blink(stone * 2024, n - 1)


def solve(stones, *, blinks):
    return sum(blink(stone, blinks) for stone in stones)


def part_1(stones):
    return solve(stones, blinks=25)


def part_2(stones):
    return solve(stones, blinks=75)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    stones = read_input("input")
    print(part_1(stones))
    print(part_2(stones))


if __name__ == "__main__":
    main()
