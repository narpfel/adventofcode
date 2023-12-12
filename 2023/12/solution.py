#!/usr/bin/env python3

from functools import cache

EXPECTED_PART_1 = 21
EXPECTED_PART_2 = 525152


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            a, b = line.split()
            yield (
                [c if c in "#." else DONT_CARE for c in a],
                [int(n) for n in b.split(",")],
            )


class DontCare:
    def __repr__(self):
        return "'?'"

    def __str__(self):
        return "?"

    def __eq__(self, other):
        return True

    def __req__(self, other):
        return True


DONT_CARE = DontCare()


def arrangements(springs, groups):
    @cache
    def go(spring, group):
        if spring >= len(springs):
            return int(group == len(groups))
        if group == len(groups):
            return int(all(x == "." for x in springs[spring:]))
        result = 0
        if springs[spring] == ".":
            result += go(spring + 1, group)
        if (
            springs[spring:spring + groups[group] + 1]
            == [*("#" * groups[group]), *("." if len(springs) - spring > groups[group] else "")]
        ):
            result += go(spring + groups[group] + 1, group + 1)
        return result

    return go(0, 0)


def part_1(conditions):
    return sum(
        arrangements(springs, groups)
        for springs, groups in conditions
    )


def part_2(conditions):
    return part_1(
        ((springs + [DONT_CARE]) * 4 + springs, groups * 5)
        for springs, groups in conditions
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    conditions = list(read_input("input"))
    print(part_1(conditions))
    print(part_2(conditions))


if __name__ == "__main__":
    main()
