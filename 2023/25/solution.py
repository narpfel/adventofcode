#!/usr/bin/env python3

import math

import networkx

EXPECTED_PART_1 = 54


def read_input(filename):
    with open(filename) as lines:
        for line in lines:
            node, connected_nodes = line.strip().split(": ")
            for connected_node in connected_nodes.split():
                yield node, connected_node


def part_1(connections):
    graph = networkx.Graph()
    graph.add_edges_from(connections)
    cut = networkx.minimum_edge_cut(graph)
    graph.remove_edges_from(cut)
    return math.prod(
        len(component)
        for component in networkx.connected_components(graph)
    )


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
