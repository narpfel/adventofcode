#!/usr/bin/env python3

from collections import defaultdict

EASY_DIGITS = {1: 2, 4: 4, 7: 3, 8: 7}


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

        mapping = {
            digit: unpack(patterns_by_len[length])
            for digit, length in EASY_DIGITS.items()
        }

        for pattern in patterns_by_len[6]:
            if pattern.issuperset(mapping[4] | mapping[7]):
                mapping[9] = pattern
            elif not pattern.issuperset(mapping[1]):
                mapping[6] = pattern
            else:
                mapping[0] = pattern

        for pattern in patterns_by_len[5]:
            if pattern.issuperset(mapping[1]):
                mapping[3] = pattern
            elif pattern.issubset(mapping[6]):
                mapping[5] = pattern
            else:
                mapping[2] = pattern

        mapping = {v: k for k, v in mapping.items()}

        number = "".join(str(mapping[digit]) for digit in digits)

        solution_part_1 += sum(int(digit) in EASY_DIGITS for digit in number)
        solution_part_2 += int(number)

    print(solution_part_1)
    print(solution_part_2)


if __name__ == "__main__":
    main()
