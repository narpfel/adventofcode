#!/usr/bin/env pypy3

from itertools import count

MODULUS = 20201227


def read_input(filename):
    with open(filename) as lines:
        [card, door] = lines
        return int(card), int(door)


def crack_encryption_key(card, door):
    subject_number = 7
    value = 1
    for i in count(1):
        value *= subject_number
        value %= MODULUS
        if value == card:
            return pow(door, i, MODULUS)


def test_part1():
    card, door = read_input("input_test")
    assert crack_encryption_key(card, door) == 14897079


def main():
    card, door = read_input("input")
    print(crack_encryption_key(card, door))


if __name__ == "__main__":
    main()
