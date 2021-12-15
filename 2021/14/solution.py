#!/usr/bin/env python3

from collections import Counter
from itertools import pairwise


def apply_pair_insertion(template, rules, *, steps):
    pairs = Counter(map("".join, pairwise(template)))
    for _ in range(steps):
        counts = pairs.items()
        pairs = Counter()
        for pair, count in counts:
            for new_pair in rules[pair]:
                pairs[new_pair] += count
    return pairs


def solve(template, rules, *, steps):
    pairs = apply_pair_insertion(template, rules, steps=steps)
    element_counts = Counter(template[-1])
    for (element, _), count in pairs.items():
        element_counts[element] += count
    return max(element_counts.values()) - min(element_counts.values())


def main():
    with open("input") as file:
        template, rules = map(str.strip, file.read().split("\n\n"))

    rules = dict(rule.split(" -> ") for rule in rules.splitlines())
    rules = {f"{a}{b}": (f"{a}{v}", f"{v}{b}") for (a, b), v in rules.items()}

    print(solve(template, rules, steps=10))
    print(solve(template, rules, steps=40))


if __name__ == "__main__":
    main()
