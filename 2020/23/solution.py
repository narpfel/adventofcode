#!/usr/bin/env pypy3

import sys
from operator import attrgetter

sys.path.insert(0, "../../2022")
Node = __import__("20.solution").solution.Node


def read_input(filename):
    with open(filename) as file:
        return int(file.read())


def play_cups(numbers, steps):
    current = Node.from_iter(numbers)
    nodes = sorted(current, key=attrgetter("value"))

    for _ in range(steps):
        # not writing this as lists and loops improves performance by 2.7x
        removed1 = current.pop_after()
        removed2 = current.pop_after()
        removed3 = current.pop_after()
        blocked1 = removed1.value
        blocked2 = removed2.value
        blocked3 = removed3.value
        blocked4 = current.value

        dest = current.value
        while dest == blocked4 or dest == blocked1 or dest == blocked2 or dest == blocked3:
            dest -= 1
            if dest == 0:
                dest = len(nodes)
        dest_node = nodes[dest - 1]

        dest_node.insert_after(removed3)
        dest_node.insert_after(removed2)
        dest_node.insert_after(removed1)

        current = current.next

    return nodes[0]


def part_1(number, steps=100):
    node = play_cups(map(int, str(number)), steps)
    return int("".join(str(n.value) for n in node)[1:])


def test_part_1():
    cup_labels = read_input("input_test")
    assert part_1(cup_labels, 10) == 92658374
    assert part_1(cup_labels) == 67384529


def main():
    cup_labels = read_input("input")
    print(part_1(cup_labels))


if __name__ == "__main__":
    main()
