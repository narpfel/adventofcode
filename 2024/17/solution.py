#!/usr/bin/env python3

EXPECTED_PART_1 = "4,6,3,5,6,3,5,2,1,0"


def read_input(filename):
    with open(filename) as lines:
        registers, program = lines.read().split("\n\n")

    registers = [int(register.split(": ")[-1]) for register in registers.splitlines()]
    program = [int(opcode) for opcode in program.split(": ")[-1].split(",")]
    return registers, program


def combo(registers, operand):
    match operand:
        case 0 | 1 | 2 | 3:
            return operand
        case 4 | 5 | 6:
            return registers[operand - 4]
        case 7:
            assert False, "reserved"


def interpret(pc, registers, program, output):
    while pc in range(len(program)):
        instr = program[pc]
        operand = program[pc + 1]
        match instr:
            case 0:
                numerator = registers[0]
                denominator = combo(registers, operand)
                registers[0] = numerator >> denominator
            case 1:
                registers[1] ^= operand
            case 2:
                registers[1] = combo(registers, operand) & 0b111
            case 3:
                return pc + 2, registers[0] != 0, operand
            case 4:
                registers[1] ^= registers[2]
            case 5:
                output.append(combo(registers, operand) & 0b111)
            case 6:
                numerator = registers[0]
                denominator = combo(registers, operand)
                registers[1] = numerator >> denominator
            case 7:
                numerator = registers[0]
                denominator = combo(registers, operand)
                registers[2] = numerator >> denominator
        pc += 2
    return pc, False, None


def part_1(puzzle_input):
    registers, program = puzzle_input
    registers = list(registers)
    output = []
    pc = 0
    while pc in range(len(program)):
        pc, should_jump, jump_target = interpret(pc, registers, program, output)
        if should_jump:
            pc = jump_target
    return ",".join(map(str, output))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    puzzle_input = read_input("input")
    print(part_1(puzzle_input))


if __name__ == "__main__":
    main()
