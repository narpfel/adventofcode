from numbers import Number
from collections import UserList
from itertools import islice, cycle, count, repeat, chain
from functools import reduce
from operator import xor
from binascii import hexlify


INPUT = "106,16,254,226,55,2,1,166,177,247,93,0,255,228,60,36"

PART_1 = [int(n) for n in INPUT.split(",")]
PART_2 = [ord(c) for c in INPUT]


class CyclicList(UserList):
    def __getitem__(self, item):
        if isinstance(item, Number):
            return super().__getitem__(item % len(self))
        elif isinstance(item, slice):
            return list(islice(
                cycle(self),
                item.start,
                item.stop if item.stop is not None else len(self),
                item.step
            ))
        else:
            raise TypeError(f"Subscript must be numeric or slice, not `{type(item)}`.")

    def __setitem__(self, index, item):
        if isinstance(index, Number):
            super().__setitem__(index % len(self), item)
        elif isinstance(index, slice):
            for i, value in zip(
                range(
                    index.start if index.start is not None else 0,
                    index.stop if index.stop is not None else len(self),
                    index.step if index.step is not None else 1,
                ),
                item
            ):
                self[i] = value
        else:
            raise TypeError(f"index must be numeric or slice, not `{type(index)}`.")

    def reverse(self, slice):
        self[slice] = reversed(self[slice])


def calculate_dense_hash(numbers):
    for chunk in zip(*([iter(numbers)] * 16)):
        yield reduce(xor, chunk, 0)


def knot_hash(input_bytes):
    index = 0
    numbers = CyclicList(range(256))
    for skip, length in zip(
        count(),
        chain.from_iterable(repeat(list(chain(input_bytes, [17, 31, 73, 47, 23])), 64))
    ):
        numbers.reverse(slice(index, index + length))
        index += length + skip
        index %= len(numbers)
    return hexlify(bytes(calculate_dense_hash(list(numbers[:])))).decode("ascii")


def main():
    numbers = CyclicList(range(256))
    index = 0
    for skip, length in zip(count(), PART_1):
        numbers.reverse(slice(index, index + length))
        index += length + skip
    print(numbers[0] * numbers[1])

    print(knot_hash(PART_2))


if __name__ == "__main__":
    main()
