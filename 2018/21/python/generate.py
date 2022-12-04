#!/usr/bin/env python3

def main():
    with open("input") as lines:
        ip = next(lines).strip().split()[1]
        instrs = [line.split() for line in lines]

    code_for_instr = {
        "addr": "r{0} + r{1}",
        "addi": "r{0} + {1}",
        "mulr": "r{0} * r{1}",
        "muli": "r{0} * {1}",
        "banr": "r{0} & r{1}",
        "bani": "r{0} & {1}",
        "borr": "r{0} | r{1}",
        "bori": "r{0} | {1}",
        "setr": "r{0}",
        "seti": "{0}",
        "gtir": "int({0} > r{1})",
        "gtri": "int(r{0} > {1})",
        "gtrr": "int(r{0} > r{1})",
        "eqir": "int({0} == r{1})",
        "eqri": "int(r{0} == {1})",
        "eqrr": "int(r{0} == r{1})",
    }

    print(
        """\
#!/usr/bin/env pypy3

def main():
    seen = set()
    last = 0

    r0 = 0
    r1 = 0
    r2 = 0
    r3 = 0
    r4 = 0
    r5 = 0

    while True:
        """.strip(),
    )

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        print(f"        if r{ip} == {i}:")
        if i == 28:
            print(
                "            if not seen:\n"
                "                print(r1)\n"
                "            if r1 in seen:\n"
                '                print(last)\n'
                "                return\n"
                "            seen.add(r1)\n"
                "            last = r1",
            )
        print(f"            r{tgt} = {code_for_instr[instr].format(lhs, rhs)}")
        print(f"            r{ip} += 1")

    print('\n\nif __name__ == "__main__":\n    main()')


if __name__ == "__main__":
    main()
