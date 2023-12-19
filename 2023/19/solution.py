#!/usr/bin/env python3

import operator
from collections import namedtuple

EXPECTED_PART_1 = 19114


COMPARISON_OPERATORS = {
    "<": operator.lt,
    ">": operator.gt,
    "?": lambda _a, _b: True,
}


Rule = namedtuple("Rule", "prop, op, n, tgt")


def parse_rule(rule):
    name, rules = rule.split("{")
    rules = rules.strip("}").split(",")
    parsed_rules = []
    for rule in rules:
        if "<" in rule:
            prop, op, n = rule.partition("<")
            n, _, tgt = n.partition(":")
        elif ">" in rule:
            prop, op, n = rule.partition(">")
            n, _, tgt = n.partition(":")
        else:
            prop = "a"
            op = "?"
            tgt = rule
        parsed_rules.append(Rule(prop=prop, op=op, n=int(n), tgt=tgt))
    return name, parsed_rules


def parse_part(s):
    part = {}
    for prop in s.strip("{}").split(","):
        name, value = prop.split("=")
        part[name] = int(value)
    return part


def read_input(filename):
    with open(filename) as lines:
        rules, parts = lines.read().split("\n\n")
        rules = dict(parse_rule(rule) for rule in rules.splitlines())
        parts = [parse_part(line) for line in parts.splitlines()]
        return rules, parts


def part_1(rules, parts):
    accepted = []

    for part in parts:
        state = "in"
        while True:
            for rule in rules[state]:
                if COMPARISON_OPERATORS[rule.op](part[rule.prop], rule.n):
                    state = rule.tgt
                    break
            else:
                assert False, rules[state]
            if state == "A":
                accepted.append(part)
                break
            elif state == "R":
                break

    return sum(
        sum(part.values())
        for part in accepted
    )


def test_part_1():
    rules, parts = read_input("input_test")
    assert part_1(rules, parts) == EXPECTED_PART_1


def main():
    rules, parts = read_input("input")
    print(part_1(rules, parts))


if __name__ == "__main__":
    main()
