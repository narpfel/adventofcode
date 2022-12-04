#!/usr/bin/env pypy3

EXECUTE = {
    "addr": lambda registers, lhs, rhs: registers[lhs] + registers[rhs],
    "addi": lambda registers, lhs, rhs: registers[lhs] + rhs,
    "mulr": lambda registers, lhs, rhs: registers[lhs] * registers[rhs],
    "muli": lambda registers, lhs, rhs: registers[lhs] * rhs,
    "banr": lambda registers, lhs, rhs: registers[lhs] & registers[rhs],
    "bani": lambda registers, lhs, rhs: registers[lhs] & rhs,
    "borr": lambda registers, lhs, rhs: registers[lhs] | registers[rhs],
    "bori": lambda registers, lhs, rhs: registers[lhs] | rhs,
    "setr": lambda registers, lhs, _: registers[lhs],
    "seti": lambda __, lhs, _: lhs,
    "gtir": lambda registers, lhs, rhs: int(lhs > registers[rhs]),
    "gtri": lambda registers, lhs, rhs: int(registers[lhs] > rhs),
    "gtrr": lambda registers, lhs, rhs: int(registers[lhs] > registers[rhs]),
    "eqir": lambda registers, lhs, rhs: int(lhs == registers[rhs]),
    "eqri": lambda registers, lhs, rhs: int(registers[lhs] == rhs),
    "eqrr": lambda registers, lhs, rhs: int(registers[lhs] == registers[rhs]),
}


def parse(line):
    instr, *args = line.split()
    return EXECUTE[instr], *[int(arg) for arg in args]


def run(instrs, ip):
    registers = [0] * 6
    while True:
        if registers[ip] == 28:
            print(registers[1])
            return
        if registers[ip] not in range(len(instrs)):
            raise AssertionError("unreachable")
        instr, lhs, rhs, tgt = instrs[registers[ip]]
        registers[tgt] = instr(registers, lhs, rhs)
        registers[ip] += 1


def main():
    with open("input") as lines:
        ip = int(next(lines).split()[1])
        instrs = [parse(line) for line in lines]

    run(instrs, ip)


if __name__ == "__main__":
    main()
