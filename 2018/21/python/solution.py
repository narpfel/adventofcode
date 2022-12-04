#!/usr/bin/env pypy3

EXECUTE = {
    "addr": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] + registers[{rhs}])",
    "addi": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] + {rhs})",
    "mulr": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] * registers[{rhs}])",
    "muli": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] * {rhs})",
    "banr": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] & registers[{rhs}])",
    "bani": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] & {rhs})",
    "borr": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] | registers[{rhs}])",
    "bori": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}] | {rhs})",
    "setr": "lambda registers: registers.__setitem__({tgt}, registers[{lhs}])",
    "seti": "lambda registers: registers.__setitem__({tgt}, {lhs})",
    "gtir": "lambda registers: registers.__setitem__({tgt}, int({lhs} > registers[{rhs}]))",
    "gtri": "lambda registers: registers.__setitem__({tgt}, int(registers[{lhs}] > {rhs}))",
    "gtrr": "lambda registers: registers.__setitem__({tgt}, int(registers[{lhs}] > registers[{rhs}]))",  # noqa: E501
    "eqir": "lambda registers: registers.__setitem__({tgt}, int({lhs} == registers[{rhs}]))",
    "eqri": "lambda registers: registers.__setitem__({tgt}, int(registers[{lhs}] == {rhs}))",
    "eqrr": "lambda registers: registers.__setitem__({tgt}, int(registers[{lhs}] == registers[{rhs}]))",  # noqa: E501
}


def parse(line):
    instr, *args = line.split()
    lhs, rhs, tgt = (int(arg) for arg in args)
    return eval(EXECUTE[instr].format(lhs=lhs, rhs=rhs, tgt=tgt))


def run(instrs, ip):
    seen = set()
    last = None
    registers = [0] * 6
    while True:
        if registers[ip] == 28:
            if not seen:
                print(registers[1])
            if registers[1] in seen:
                print(last)
                return
            seen.add(registers[1])
            last = registers[1]
        if registers[ip] not in range(len(instrs)):
            raise AssertionError("unreachable")
        instrs[registers[ip]](registers)
        registers[ip] += 1


def main():
    with open("input") as lines:
        ip = int(next(lines).split()[1])
        instrs = [parse(line) for line in lines]

    run(instrs, ip)


if __name__ == "__main__":
    main()
