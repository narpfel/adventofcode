#!/usr/bin/env pypy3

EXPECTED_PART_1 = 3
EXPECTED_PART_2 = 1623178306

DECRYPTION_KEY = 811589153


def read_input(filename):
    with open(filename) as lines:
        return [int(line) for line in lines]


class Node:
    __slots__ = "prev", "value", "next"

    def __init__(self, prev, value, next):
        self.prev = prev
        self.value = value
        self.next = next

    @classmethod
    def from_iter(cls, iterable):
        it = iter(iterable)
        last = first = Node(None, next(it), None)
        for value in it:
            node = Node(None, value, None)
            last.insert_after(node)
            last = node
        first.prev = last
        last.next = first
        return first

    def insert_before(self, node):
        node.prev = self.prev
        node.next = self
        if self.prev is not None:
            self.prev.next = node
        self.prev = node

    def insert_after(self, node):
        node.prev = self
        node.next = self.next
        if self.next is not None:
            self.next.prev = node
        self.next = node

    def pop_after(self):
        node = self.next
        node.remove()
        return node

    def remove(self):
        self.prev.next = self.next
        self.next.prev = self.prev
        self.next = None
        self.prev = None

    def __iter__(self):
        begin = self
        current = self
        while True:
            yield current
            current = current.next
            if current is begin:
                return


def mix(numbers, *, repeat=1):
    numbers = Node.from_iter(numbers)
    nodes = list(numbers)
    max_swaps = len(nodes) - 1

    for _ in range(repeat):
        for node in nodes:
            target = node
            if node.value > 0:
                swaps = node.value % max_swaps
                for _ in range(swaps):
                    target = target.next
                if swaps != 0:
                    node.remove()
                    target.insert_after(node)
            elif node.value < 0:
                swaps = -node.value % max_swaps
                for _ in range(swaps):
                    target = target.prev
                if swaps != 0:
                    node.remove()
                    target.insert_before(node)

    node = next(number for number in numbers if number.value == 0)
    result = 0
    for _ in range(3):
        for _ in range(1000):
            node = node.next
        result += node.value
    return result


def part_2(numbers):
    return mix((n * DECRYPTION_KEY for n in numbers), repeat=10)


def test_part_1():
    numbers = read_input("input_test")
    assert mix(numbers) == EXPECTED_PART_1


def test_part_2():
    numbers = read_input("input_test")
    assert part_2(numbers) == EXPECTED_PART_2


def main():
    numbers = read_input("input")
    print(mix(numbers))
    print(part_2(numbers))


if __name__ == "__main__":
    main()
