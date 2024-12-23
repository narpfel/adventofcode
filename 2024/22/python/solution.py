#!/usr/bin/env pypy3

from collections import Counter

EXPECTED_PART_1 = 37327623
EXPECTED_PART_2 = 23

PRUNE_MODULUS = 16777216


def read_input(filename):
    with open(filename) as lines:
        return [int(line) for line in lines]


def next_secret_number(n):
    n = (n ^ n * 64) % PRUNE_MODULUS
    n = (n ^ n // 32) % PRUNE_MODULUS
    n = (n ^ n * 2048) % PRUNE_MODULUS
    return n


def nth_secret_number(*, secret_number, n):
    for _ in range(n):
        secret_number = next_secret_number(secret_number)
    return secret_number


def part_1(secret_numbers):
    return sum(
        nth_secret_number(secret_number=secret, n=2000)
        for secret in secret_numbers
    )


def part_2(secret_numbers):
    total_bananas = Counter()
    for secret in secret_numbers:
        changes = 0
        bananas_by_sequence = {}
        for i in range(2000):
            new_secret = next_secret_number(secret)
            change = (new_secret % 10) - (secret % 10)
            # pack the last 4 changes into a single integer to speed up hashing
            changes *= 20
            changes += change + 10
            changes %= 20 ** 4
            secret = new_secret
            if i >= 3 and changes not in bananas_by_sequence:
                bananas_by_sequence[changes] = secret % 10
        total_bananas.update(bananas_by_sequence)
    return max(total_bananas.values())


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test_2")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    secret_numbers = read_input("input")
    print(part_1(secret_numbers))
    print(part_2(secret_numbers))


if __name__ == "__main__":
    main()
