#!/usr/bin/env python3

from pathlib import Path


def part1(commands):
    position = 0
    depth = 0
    for command, arg in commands:
        if command == "forward":
            position += int(arg)
        elif command == "down":
            depth += int(arg)
        elif command == "up":
            depth -= int(arg)
        else:
            raise AssertionError(f"unknown command {command!r}")
    return position * depth


def part2(commands):
    position = 0
    depth = 0
    aim = 0
    for command, arg in commands:
        if command == "forward":
            position += int(arg)
            depth += aim * int(arg)
        elif command == "down":
            aim += int(arg)
        elif command == "up":
            aim -= int(arg)
        else:
            raise AssertionError(f"unknown command {command!r}")
    return position * depth


def main():
    commands = list(map(str.split, Path("input").read_text().splitlines()))
    print(part1(commands))
    print(part2(commands))


if __name__ == "__main__":
    main()
