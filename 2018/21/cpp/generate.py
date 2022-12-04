#!/usr/bin/env python3

def main():
    with open("input") as lines:
        ip = next(lines).strip().split()[1]
        instrs = [line.split() for line in lines]

    max_ip = len(instrs)

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
        "eqir": "{0} == r{1}",
        "eqri": "r{0} == {1}",
        "eqrr": "r{0} == r{1}",
    }

    print(
        """
#include <cstdint>

#include <unordered_set>

#include <fmt/format.h>

auto main() -> int {
    auto seen = std::unordered_set<std::uint64_t>{};
    auto last = std::uint64_t{};

    auto r0 = std::uint64_t{0};
    auto r1 = std::uint64_t{0};
    auto r2 = std::uint64_t{0};
    auto r3 = std::uint64_t{0};
    auto r4 = std::uint64_t{0};
    auto r5 = std::uint64_t{0};
        """.strip(),
    )

    print("\n    static void* labels[] = {")
    for i in range(len(instrs)):
        print(f"        &&label_{i},")
    print("    };\n")

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        print(f"label_{i}:")
        if i == 28:
            print(
                "    if (seen.empty()) {\n"
                '        fmt::print("{}\\n", r1);\n'
                "    }\n"
                "    if (not seen.emplace(r1).second) {\n"
                '        fmt::print("{}\\n", last);\n'
                "        return 0;\n"
                "    }\n"
                "    last = r1;",
            )
        if ip in {lhs, rhs, tgt}:
            print(f"    r{ip} = {i};")
        print(f"    r{tgt} = {code_for_instr[instr].format(lhs, rhs)};")
        if tgt == ip:
            print(
                f"    r{ip} += 1;\n"
                f'    if (r{ip} >= {max_ip}) {{ return 1; }}\n'
                f"    goto *labels[r{ip}];",
            )

    print("}")


if __name__ == "__main__":
    main()
