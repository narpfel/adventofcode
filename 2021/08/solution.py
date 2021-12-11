#!/usr/bin/env python3

from collections import defaultdict

EASY_DIGITS = {1: 2, 4: 4, 7: 3, 8: 7}

SEVEN_SEGMENT_DIGITS = {
    frozenset("abcefg"): 0,
    frozenset("cf"): 1,
    frozenset("acdeg"): 2,
    frozenset("acdfg"): 3,
    frozenset("bcdf"): 4,
    frozenset("abdfg"): 5,
    frozenset("abdefg"): 6,
    frozenset("acf"): 7,
    frozenset("abcdefg"): 8,
    frozenset("abcdfg"): 9,
}


def unpack(xs):
    result, = xs
    return result


def main():
    with open("input") as lines:
        patterns_and_digits = [
            tuple(map(lambda s: list(map(frozenset, s.split())), line.split(" | ")))
            for line in lines
        ]

    solution_part_1 = 0
    solution_part_2 = 0

    for patterns, digits in patterns_and_digits:
        patterns_by_len = defaultdict(list)
        for pattern in patterns:
            patterns_by_len[len(pattern)].append(pattern)
        one, four, seven, eight = (
            unpack(patterns_by_len[length])
            for length in EASY_DIGITS.values()
        )

        wire_map = {unpack(seven - one): "a"}

        overlap_4_7 = four | seven
        for pattern in patterns_by_len[6]:
            if pattern.issuperset(overlap_4_7):
                g = unpack(pattern - overlap_4_7)
                wire_map[g] = "g"

        seven_and_g = seven.union(g)
        for pattern in patterns_by_len[5]:
            if pattern.issuperset(seven_and_g):
                wire_map[unpack(pattern - seven_and_g)] = "d"

        one_and_adg = one.union(wire_map)
        for pattern in patterns_by_len[6]:
            if pattern.issuperset(one_and_adg):
                wire_map[unpack(pattern - one_and_adg)] = "b"

        one_and_adgb = one.union(wire_map)
        for pattern in patterns_by_len[6]:
            if len(pattern - one_and_adgb) == 1:
                wire_map[unpack(pattern - one_and_adgb)] = "e"

        for pattern in patterns_by_len[6]:
            if pattern.issuperset(wire_map):
                wire_map[unpack(pattern - set(wire_map))] = "f"

        wire_map[unpack(eight - set(wire_map))] = "c"

        number = "".join(
            str(SEVEN_SEGMENT_DIGITS[frozenset("".join(wire_map[wire] for wire in wires))])
            for wires in digits
        )
        solution_part_1 += sum(int(digit) in EASY_DIGITS for digit in number)
        solution_part_2 += int(number)

    print(solution_part_1)
    print(solution_part_2)


if __name__ == "__main__":
    main()
