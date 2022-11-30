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
    return instr, *[int(arg) for arg in args]


def run(instrs, ip, r0):
    registers = [0] * 6
    registers[0] = r0
    while registers[ip] in range(len(instrs)):
        instr, lhs, rhs, tgt = instrs[registers[ip]]
        # part 2: we need to find the sum of the divisors of r1; the last instruction is
        # only executed for part 2
        if registers[ip] == len(instrs) - 1:
            r1 = registers[1]
            divisor_sum = 0
            for i in range(1, r1 + 1):
                if r1 % i == 0:
                    divisor_sum += i
            return divisor_sum
        registers[tgt] = EXECUTE[instr](registers, lhs, rhs)
        registers[ip] += 1
    return registers[0]


def main():
    with open("input") as lines:
        ip = int(next(lines).split()[1])
        instrs = [parse(line) for line in lines]

    print(run(instrs, ip, 0))
    print(run(instrs, ip, 1))


if __name__ == "__main__":
    main()
