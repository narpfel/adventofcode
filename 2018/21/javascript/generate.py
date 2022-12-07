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
        "gtir": "{0} > r{1}",
        "gtri": "r{0} > {1}",
        "gtrr": "r{0} > r{1}",
        "eqir": "{0} === r{1}",
        "eqri": "r{0} === {1}",
        "eqrr": "r{0} === r{1}",
    }

    print(
        """
#!/usr/bin/env node

const main = () => {
    const seen = new Set();
    let last = 0;

    let r0 = 0;
    let r1 = 0;
    let r2 = 0;
    let r3 = 0;
    let r4 = 0;
    let r5 = 0;

    while (true) {
        """.strip(),
    )

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        print(f"        if (r{ip} === {i}) {{")
        if i == 28:
            print(
                "            if (seen.size === 0) {\n"
                '                console.log("%d", r1);\n'
                "            }\n"
                "            if (seen.has(r1)) {\n"
                '                console.log("%d", last);\n'
                "                return;\n"
                "            }\n"
                "            seen.add(r1);\n"
                "            last = r1;",
            )
        print(f"            r{tgt} = {code_for_instr[instr].format(lhs, rhs)};")
        print(f"            r{ip} += 1;")
        print("        }")

    print("    }")
    print("}")
    print("\nmain();")


if __name__ == "__main__":
    main()
