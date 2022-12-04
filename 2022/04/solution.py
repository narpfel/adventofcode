#!/usr/bin/env python3

EXPECTED_PART_1 = 2


def inclusive_range(lo, hi):
    return range(lo, hi + 1)


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            a, b = line.split(",")
            yield (
                set(inclusive_range(*map(int, a.split("-")))),
                set(inclusive_range(*map(int, b.split("-")))),
            )


def part_1(assignments):
    return sum(lhs >= rhs or rhs >= lhs for lhs, rhs in assignments)


def test_part_1():
    assignments = read_input("input_test")
    assert part_1(assignments) == EXPECTED_PART_1


def main():
    assignments = list(read_input("input"))
    print(part_1(assignments))


if __name__ == "__main__":
    main()
