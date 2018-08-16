#!/usr/bin/env python3

from hashlib import md5
from itertools import count, islice


INPUT = b"reyedfim"


def byte_after_leading_zeroes(leading_zeroes):
    for n in count():
        hash = md5()
        hash.update(INPUT + str(n).encode())
        digest = hash.hexdigest()
        if digest.startswith("0" * leading_zeroes):
            yield digest[leading_zeroes], digest[leading_zeroes + 1]


def main():
    print("".join(byte for byte, _ in islice(byte_after_leading_zeroes(5), 8)))

    password = {}
    for position, byte in byte_after_leading_zeroes(5):
        try:
            position = int(position)
        except ValueError:
            pass
        else:
            if position in range(8):
                password.setdefault(position, byte)
        if len(password) == 8:
            print("".join(byte for _, byte in sorted(password.items())))
            break


if __name__ == '__main__':
    main()
