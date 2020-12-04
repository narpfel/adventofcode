#!/usr/bin/env python3

def is_valid_part1(low, high, char, password):
    return password.count(char) in range(low, high + 1)


def is_valid_part2(i, j, char, password):
    return (password[i - 1] == char) != (password[j - 1] == char)


def parse(line):
    range_, (char, _), password = line.split()
    low, high = map(int, range_.split("-"))
    return low, high, char, password


def solve(lines, is_valid):
    return sum(is_valid(*parse(line)) for line in lines)


def main():
    with open("input") as lines:
        lines = list(lines)

    print(solve(lines, is_valid_part1))
    print(solve(lines, is_valid_part2))


if __name__ == "__main__":
    main()
