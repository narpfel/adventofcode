#!/usr/bin/env python3

EXPECTED_PART_1 = 11


def read_input(filename):
    with open(filename) as lines:
        return zip(*(list(map(int, line.split())) for line in lines))


def part_1(location_id_lists):
    lhs, rhs = map(sorted, location_id_lists)
    return sum(abs(x - y) for x, y in zip(lhs, rhs))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
