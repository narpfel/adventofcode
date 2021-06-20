#!/usr/bin/env pypy3
from itertools import count

from _md5 import md5

INPUT = b"reyedfim"


def byte_after_leading_zeroes(leading_zeroes_count):
    leading_zeroes = "0" * leading_zeroes_count
    for n in count():
        hash = md5()
        hash.update(INPUT + str(n).encode())
        digest = hash.hexdigest()
        if digest.startswith(leading_zeroes):
            yield digest[leading_zeroes_count], digest[leading_zeroes_count + 1]


def main():
    part1 = []
    part2 = {}

    for position, byte in byte_after_leading_zeroes(5):
        if len(part1) < 8:
            part1.append(position)
        if '0' <= position < '8':
            part2.setdefault(position, byte)
        if len(part2) == 8:
            break

    print("".join(part1))
    print("".join(byte for _, byte in sorted(part2.items())))


if __name__ == "__main__":
    main()
