#!/usr/bin/env pypy3

EXPECTED_PART_1 = 1928


def read_input(filename):
    with open(filename) as lines:
        block_lengths = [int(char) for char in lines.read().strip()]

    blocks = []
    for i, size in enumerate(block_lengths):
        blocks.extend([EMPTY if i % 2 == 1 else i // 2] * size)
    return blocks


class Empty:
    def __repr__(self):
        return "."


EMPTY = Empty()


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


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
