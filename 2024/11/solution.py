#!/usr/bin/env python3

EXPECTED_PART_1 = 55312


def read_input(filename):
    with open(filename) as lines:
        return [int(number) for number in lines.read().split()]


def part_1(stones):
    for _ in range(25):
        new_stones = []
        for stone in stones:
            if stone == 0:
                new_stones.append(1)
            else:
                s = str(stone)
                if len(s) % 2 == 0:
                    new_stones.append(int(s[:len(s) // 2]))
                    new_stones.append(int(s[len(s) // 2:]))
                else:
                    new_stones.append(stone * 2024)
        stones = new_stones
    return len(stones)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    stones = read_input("input")
    print(part_1(stones))


if __name__ == "__main__":
    main()
