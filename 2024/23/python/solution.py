#!/usr/bin/env python3

from collections import defaultdict

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


def bron_kerbosch(connections, r, p):
    yield r
    while p:
        v = next(iter(p))
        yield from bron_kerbosch(connections, r | {v}, p & connections[v])
        p.discard(v)


def solve(connections):
    part_1_result = 0
    longest_clique = set()
    for clique in bron_kerbosch(connections, frozenset(), set(connections)):
        if len(clique) == 3 and any(c.startswith("t") for c in clique):
            part_1_result += 1
        longest_clique = max(longest_clique, clique, key=len)
    return part_1_result, ",".join(sorted(longest_clique))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[0] == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert solve(puzzle_input)[1] == EXPECTED_PART_2


def main():
    connections = read_input("input")
    part_1, part_2 = solve(connections)
    print(part_1)
    print(part_2)


if __name__ == "__main__":
    main()
