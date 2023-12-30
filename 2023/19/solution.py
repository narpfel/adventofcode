#!/usr/bin/env python3

import math
import operator
from collections import namedtuple

EXPECTED_PART_1 = 19114
EXPECTED_PART_2 = 167409079868000


COMPARISON_OPERATORS = {
    "<": operator.lt,
    ">": operator.gt,
    "?": lambda _a, _b: True,
}


Rule = namedtuple("Rule", "prop, op, value, tgt")


def parse_rule(rule):
    name, rules = rule.split("{")
    rules = rules.strip("}").split(",")
    parsed_rules = []
    for rule in rules:
        if "<" in rule:
            prop, op, value = rule.partition("<")
            value, _, tgt = value.partition(":")
        elif ">" in rule:
            prop, op, value = rule.partition(">")
            value, _, tgt = value.partition(":")
        else:
            prop = "a"
            op = "?"
            tgt = rule
            value = 0
        parsed_rules.append(Rule(prop=prop, op=op, value=int(value), tgt=tgt))
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
                if COMPARISON_OPERATORS[rule.op](part[rule.prop], rule.value):
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


def split_range_at(rng, mid):
    start = rng.start
    stop = rng.stop
    return range(start, min(stop, mid)), range(max(mid, start), stop)


def accepted_parts(rules, part, state, rule_index):
    while True:
        if state == "A":
            yield part
            return
        elif state == "R":
            return

        rule = rules[state][rule_index]
        match rule.op:
            case "<" | ">":
                if rule.op == "<":
                    inside, outside = split_range_at(part[rule.prop], rule.value)
                else:
                    outside, inside = split_range_at(part[rule.prop], rule.value + 1)
                part_outside = part | {rule.prop: outside}
                yield from accepted_parts(rules, part_outside, state, rule_index + 1)
                part = part | {rule.prop: inside}
            case "?":
                pass
            case _:
                assert False, rule

        state = rule.tgt
        rule_index = 0


def part_2(rules):
    part = dict(x=range(1, 4001), m=range(1, 4001), a=range(1, 4001), s=range(1, 4001))
    return sum(
        math.prod(len(prop) for prop in part.values())
        for part in accepted_parts(rules, part, "in", 0)
    )


def test_part_1():
    rules, parts = read_input("input_test")
    assert part_1(rules, parts) == EXPECTED_PART_1


def test_part_2():
    rules, _ = read_input("input_test")
    assert part_2(rules) == EXPECTED_PART_2


def main():
    rules, parts = read_input("input")
    print(part_1(rules, parts))
    print(part_2(rules))


if __name__ == "__main__":
    main()
