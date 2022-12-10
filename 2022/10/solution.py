#!/usr/bin/env python3

EXPECTED_PART_1 = 13140
EXPECTED_PART_2 = (
    "██  ██  ██  ██  ██  ██  ██  ██  ██  ██  \n"
    "███   ███   ███   ███   ███   ███   ███ \n"
    "████    ████    ████    ████    ████    \n"
    "█████     █████     █████     █████     \n"
    "██████      ██████      ██████      ████\n"
    "███████       ███████       ███████     "
)

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

    def draw_pixel():
        if cycle % 40 == 0:
            pixels.append([])
        if cycle % 40 in {x - 1, x, x + 1}:
            pixels[-1].append("█")
        else:
            pixels[-1].append(" ")

    x = 1
    cycle = 0
    signal_strengths = []
    pixels = []

    for instruction in instructions:
        match instruction:
            case "noop":
                draw_pixel()
                cycle += 1
                record_signal_strength()
            case "addx", value:
                draw_pixel()
                cycle += 1
                record_signal_strength()
                draw_pixel()
                cycle += 1
                record_signal_strength()
                x += value

    return sum(signal_strengths), "\n".join("".join(line) for line in pixels)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert run(puzzle_input)[0] == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert run(puzzle_input)[1] == EXPECTED_PART_2


def main():
    instructions = read_input("input")
    part_1, part_2 = run(instructions)
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
