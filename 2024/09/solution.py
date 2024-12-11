#!/usr/bin/env pypy3

from itertools import groupby

EXPECTED_PART_1 = 1928
EXPECTED_PART_2 = 2858


class Empty:
    def __repr__(self):
        return "."


EMPTY = Empty()


def read_input(filename):
    with open(filename) as file:
        blocks = []
        for i, size in enumerate(map(int, file.read().strip())):
            blocks.extend([EMPTY if i % 2 == 1 else i // 2] * size)
        return blocks


def checksum(blocks):
    return sum(i * block for i, block in enumerate(blocks) if block is not EMPTY)


def part_1(blocks):
    blocks = list(blocks)
    i = 0
    j = -1
    while i < (len(blocks) + j + 1):
        while blocks[j] is EMPTY:
            j -= 1
        assert blocks[j] is not EMPTY

        if blocks[i] is EMPTY:
            blocks[i], blocks[j] = blocks[j], blocks[i]
            j -= 1
        i += 1

    return checksum(blocks)


def ilen(iterable):
    # This manual loop is faster on pypy.
    length = 0
    for _ in iterable:
        length += 1
    return length


def split_into_files(blocks):
    files = []
    empties = []
    position = 0

    for val, group in groupby(blocks):
        length = ilen(group)
        (empties if val is EMPTY else files).append((position, length))
        position += length

    return files, empties


def fill_next_empty_by_length(next_empty_by_length, empties, start_index):
    for i in range(start_index, len(empties)):
        _, length = empties[i]
        for l in range(length + 1):  # noqa: E741 (`l` is not an ambiguous variable name)
            if l not in next_empty_by_length:
                next_empty_by_length[l] = i
        if len(next_empty_by_length) == 10:
            return


def part_2(blocks):
    blocks = list(blocks)
    files, empties = split_into_files(blocks)

    next_empty_by_length = {}
    fill_next_empty_by_length(next_empty_by_length, empties, 0)

    for pos, length in reversed(files):
        i = next_empty_by_length.pop(length, None)
        if i is None:
            continue

        empty_pos, empty_length = empties[i]

        if empty_pos >= pos:
            continue

        for j in range(10):
            if next_empty_by_length.get(j) == i:
                del next_empty_by_length[j]

        assert empty_length >= length
        blocks[empty_pos:empty_pos+length], blocks[pos:pos+length] = (
            blocks[pos:pos+length], blocks[empty_pos:empty_pos+length],
        )
        empties[i] = (empty_pos + length, empty_length - length)

        fill_next_empty_by_length(next_empty_by_length, empties, max(0, i - 1))

    return checksum(blocks)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))
    print(part_2(puzzle_input))


if __name__ == "__main__":
    main()
