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
        "banr": "bit.band(r{0}, r{1}",
        "bani": "bit.band(r{0}, {1})",
        "borr": "bit.bor(r{0}, r{1})",
        "bori": "bit.bor(r{0}, {1})",
        "setr": "r{0}",
        "seti": "{0}",
        "gtir": "({0} > r{1}) and 1 or 0",
        "gtri": "(r{0} > {1}) and 1 or 0",
        "gtrr": "(r{0} > r{1}) and 1 or 0",
        "eqir": "({0} == r{1}) and 1 or 0",
        "eqri": "(r{0} == {1}) and 1 or 0",
        "eqrr": "(r{0} == r{1}) and 1 or 0",
    }

    print(
        """\
#!/usr/bin/env luajit

function main()
    local seen = {}
    local last = 0

    local r0 = 0
    local r1 = 0
    local r2 = 0
    local r3 = 0
    local r4 = 0
    local r5 = 0

    while true do
        """.strip(),
    )

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        print(f"        if r{ip} == {i} then")
        if i == 28:
            print(
                "            if next(seen) == nil then\n"
                "                print(r1)\n"
                "            end\n"
                "            if seen[r1] then\n"
                '                print(last)\n'
                "                return\n"
                "            end\n"
                "            seen[r1] = true\n"
                "            last = r1",
            )
        print(f"            r{tgt} = {code_for_instr[instr].format(lhs, rhs)}")
        print(f"            r{ip} = r{ip} + 1")
        print("        end")

    print("    end")
    print("end")

    print('\nmain()')


if __name__ == "__main__":
    main()
