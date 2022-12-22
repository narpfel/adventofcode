#!/usr/bin/env pypy

from rpython.rlib import jit

driver = jit.JitDriver(
    greens=["ip", "ip_value", "instrs"],
    reds=["last", "registers", "seen"],
    virtualizables=[],
    is_recursive=False,
)

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
    instr, lhs, rhs, tgt = line.split(" ")
    return instr, int(lhs), int(rhs), int(tgt)


@jit.purefunction
def lookup_instr(functions, opcode):
    return functions[opcode]


def run(instrs, ip):
    seen = {}
    last = 0
    registers = [0] * 6
    assert 0 <= ip < len(registers)
    while True:
        driver.jit_merge_point(
            ip=ip,
            ip_value=registers[ip],
            instrs=instrs,
            last=last,
            registers=registers,
            seen=seen,
        )
        if registers[ip] == 28:
            if not seen:
                print(registers[1])
            if registers[1] in seen:
                print(last)
                return
            seen[registers[1]] = None
            last = registers[1]
        if not (0 <= registers[ip] < len(instrs)):
            raise AssertionError("unreachable")
        instr, lhs, rhs, tgt = instrs[registers[ip]]
        f = lookup_instr(EXECUTE, instr)
        registers[tgt] = f(registers, lhs, rhs)
        registers[ip] += 1


def main(argv):
    with open("input") as file:
        lines = file.read().splitlines()
        ip = int(lines[0].split(" ")[1])
        instrs = [parse(line) for line in lines[1:]]

    run(instrs, ip)

    return 0


def target(*args):
    return main


if __name__ == "__main__":
    main([])
