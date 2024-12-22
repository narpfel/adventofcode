#!/usr/bin/env pypy3

EXPECTED_PART_1 = 37327623

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


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    secret_numbers = read_input("input")
    print(part_1(secret_numbers))


if __name__ == "__main__":
    main()
