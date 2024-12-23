#!/usr/bin/env python3

from collections import defaultdict
from itertools import combinations

EXPECTED_PART_1 = 7
EXPECTED_PART_2 = "co,de,ka,ta"


def read_input(filename):
    with open(filename) as lines:
        connections = defaultdict(set)
        for line in lines:
            a, b = line.strip().split("-")
            connections[a].add(b)
            connections[b].add(a)
        return connections


def part_1(connections):
    return sum(
        1
        for c1, c2, c3 in combinations(connections, r=3)
        if (
            c1 in connections[c2]
            and c1 in connections[c3]
            and c2 in connections[c1]
            and c2 in connections[c3]
            and c3 in connections[c1]
            and c3 in connections[c2]
            and (
                c1.startswith("t")
                or c2.startswith("t")
                or c3.startswith("t")
            )
        )
    )


def part_2(connections):
    # I have no idea why this works, because it absolutely doesn’t find *all*
    # cliques (e. g. part 1 can’t be solved with this algorithm).
    cliques = set()
    done = set()
    for c in connections:
        if c in done:
            continue
        todo = set(connections[c])
        seen = {c}
        while todo:
            c = todo.pop()
            if all(c in connections[s] for s in seen):
                seen.add(c)
                todo.update(
                    c
                    for c in connections[c]
                    if c not in seen
                )
        cliques.add(frozenset(seen))
        done.update(seen)
    return ",".join(sorted(max(cliques, key=len)))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    connections = read_input("input")
    print(part_1(connections))
    print(part_2(connections))


if __name__ == "__main__":
    main()
