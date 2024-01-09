#!/usr/bin/env python3

def main():
    with open("input") as lines:
        ip = next(lines).strip().split()[1]
        instrs = [line.split() for line in lines]

    code_for_instr = {
        "addr": "(+ r{0} r{1})",
        "addi": "(+ r{0} {1})",
        "mulr": "(* r{0} r{1})",
        "muli": "(* r{0} {1})",
        "banr": "(logand r{0} r{1})",
        "bani": "(logand r{0} {1})",
        "borr": "(logior r{0} r{1})",
        "bori": "(logior r{0} {1})",
        "setr": "r{0}",
        "seti": "{0}",
        "gtir": "(if (> {0} r{1}) 1 0)",
        "gtri": "(if (> r{0} {1}) 1 0)",
        "gtrr": "(if (> r{0} r{1}) 1 0)",
        "eqir": "(if (= {0} r{1}) 1 0)",
        "eqri": "(if (= r{0} {1}) 1 0)",
        "eqrr": "(if (= r{0} r{1}) 1 0)",
    }

    print(
        """\
#!/usr/bin/env -S sbcl --script

(defun main ()
  (let
    ((seen (make-hash-table))
     (last-seen 0)
     (r0 0)
     (r1 0)
     (r2 0)
     (r3 0)
     (r4 0)
     (r5 0))
    (loop
        """.strip(),
    )

    for i, (instr, lhs, rhs, tgt) in enumerate(instrs):
        if i != 0:
            print()
        print(f"      (when (eql r{ip} {i})")
        if i == 28:
            print(
                "        (when (eql 0 (hash-table-count seen))\n"
                "          (prin1 r1))\n"
                "        (when (gethash r1 seen)\n"
                "          (print last-seen)\n"
                "          (terpri)\n"
                "          (return))\n"
                "        (setf (gethash r1 seen) 0)\n"
                "        (setf last-seen r1)",
            )
        print(f"        (setf r{tgt} {code_for_instr[instr].format(lhs, rhs)})")
        print(f"        (setf r{ip} (+ r{ip} 1)))", end="")
    print(")))")

    print("\n(main)")


if __name__ == "__main__":
    main()
