#!/usr/bin/env python3

from itertools import cycle, islice, count


INPUT = [
    int(s)
    for s in "10    3   15  10  5   15  5   15  9   2   5   8   5   2   3   6".split()
]


class Bank:
    def __init__(self, value):
        self.value = value


def values(banks):
    return tuple(bank.value for bank in banks)


def max_position(banks):
    return max(enumerate(banks), key=lambda item: item[1].value)[0]


def main():
    banks = [Bank(value) for value in INPUT]
    seen = {}
    for i in count():
        vs = values(banks)
        if vs in seen:
            print(i)
            print(i - seen[vs])
            break
        seen[vs] = i

        max_pos = max_position(banks)
        bs = islice(cycle(banks), max_pos, None)
        b = next(bs)
        v = b.value
        b.value = 0
        for _ in range(v):
            next(bs).value += 1


if __name__ == '__main__':
    main()
