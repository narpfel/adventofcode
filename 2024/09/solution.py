#!/usr/bin/env pypy3

EXPECTED_PART_1 = 1928
EXPECTED_PART_2 = 2858


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


def part_2(blocks):
    blocks = list(blocks)
    j = -1
    while j > -len(blocks):
        while blocks[j] is EMPTY:
            j -= 1
        assert blocks[j] is not EMPTY

        k = j
        block = blocks[k]
        l = 0  # noqa: E741 (`l` is not an ambiguous variable name)
        while blocks[k] == block and k > -len(blocks):
            k -= 1
            l += 1

        for i in range(len(blocks) + j + 1):
            if blocks[i] is EMPTY and blocks[i:i+l] == [EMPTY] * l:
                blocks[i:i+l], blocks[j:k:-1] = blocks[j:k:-1], blocks[i:i+l]
                break
        j = k

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
