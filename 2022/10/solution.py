#!/usr/bin/env python3

EXPECTED_PART_1 = 13140

CYCLES = range(20, 221, 40)


def parse_instruction(line):
    match line.strip().split():
        case ["noop"]:
            return "noop"
        case ["addx", value]:
            return "addx", int(value)


def read_input(filename):
    with open(filename) as lines:
        return [parse_instruction(line) for line in lines]


def run(instructions):
    def record_signal_strength():
        if cycle in CYCLES:
            signal_strengths.append(cycle * x)

    x = 1
    cycle = 0
    signal_strengths = []

    for instruction in instructions:
        match instruction:
            case "noop":
                cycle += 1
                record_signal_strength()
            case "addx", value:
                cycle += 1
                record_signal_strength()
                cycle += 1
                record_signal_strength()
                x += value

    return sum(signal_strengths)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert run(puzzle_input) == EXPECTED_PART_1


def main():
    instructions = read_input("input")
    part_1 = run(instructions)
    print(part_1)


if __name__ == "__main__":
    main()
