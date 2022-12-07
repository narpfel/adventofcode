#!/usr/bin/env python3

def main():
    with open("input") as lines:
        ip = next(lines).strip().split()[1]
        instrs = [line.split() for line in lines]

    code_for_instr = {
        "addr": "r{0} + r{1}",
        "addi": "r{0} + {1}L",
        "mulr": "r{0} * r{1}",
        "muli": "r{0} * {1}L",
        "banr": "r{0} & r{1}",
        "bani": "r{0} & {1}L",
        "borr": "r{0} | r{1}",
        "bori": "r{0} | {1}L",
        "setr": "r{0}",
        "seti": "{0}L",
        "gtir": "{0}L > r{1} ? 1L : 0L",
        "gtri": "r{0} > {1}L ? 1L : 0L",
        "gtrr": "r{0} > r{1} ? 1L : 0L",
        "eqir": "{0}L == r{1} ? 1L : 0L",
        "eqri": "r{0} == {1}L ? 1L : 0L",
        "eqrr": "r{0} == r{1} ? 1L : 0L",
    }

    print(
        """
using System;
using System.Collections.Generic;

public class Generated {
    public static void Main(string[] args) {
        var seen = new HashSet<long>();
        var last = 0L;

        var r0 = 0L;
        var r1 = 0L;
        var r2 = 0L;
        var r3 = 0L;
        var r4 = 0L;
        var r5 = 0L;

        while (true) {
        """.strip(),
    )

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        print(f"            if (r{ip} == {i}L) {{")
        if i == 28:
            print(
                "                if (seen.Count == 0) {\n"
                '                    Console.WriteLine(r1);\n'
                "                }\n"
                "                if (seen.Contains(r1)) {\n"
                '                    Console.WriteLine(last);\n'
                "                    return;\n"
                "                }\n"
                "                seen.Add(r1);\n"
                "                last = r1;",
            )
        print(f"                r{tgt} = {code_for_instr[instr].format(lhs, rhs)};")
        print(f"                r{ip} += 1L;")
        print("            }")

    print("        }")
    print("    }")
    print("}")


if __name__ == "__main__":
    main()
