#!/usr/bin/env python3

from functools import cached_property

from attr import attrib
from attr import attrs

EXPECTED_PART_1 = 95437
EXPECTED_PART_2 = 24933642

AVAILABLE_DISK_SPACE = 70000000
NEEDED_FOR_UPDATE = 30000000


@attrs(frozen=True)
class Directory:
    name = attrib()
    parent = attrib()
    files = attrib(factory=dict)
    children = attrib(factory=dict)

    @cached_property
    def total_size(self):
        return (
            sum(self.files.values())
            + sum(child.total_size for child in self.children.values())
        )

    def add_child_dir(self, name):
        child = Directory(name=name, parent=self)
        self.children[name] = child
        return child


def read_input(filename):
    root = Directory(name="/", parent=None)
    dir = root

    with open(filename) as lines:
        for line in lines:
            line = line.strip()
            if line.startswith("$ cd "):
                dirname = line.split()[-1]
                if dirname == "/":
                    dir = root
                elif dirname == "..":
                    dir = dir.parent
                    assert dir is not None, "attempted to cd out of /"
                else:
                    dir = dir.add_child_dir(dirname)
            elif line == "$ ls":
                pass
            elif line.startswith("dir "):
                dir.add_child_dir(line.split()[-1])
            else:
                size, filename = line.split()
                dir.files[filename] = int(size)

    return root


def iter_sizes(directory):
    for child in directory.children.values():
        yield from iter_sizes(child)
    yield directory.total_size


def part_1(root):
    return sum(size for size in iter_sizes(root) if size <= 100_000)


def part_2(root):
    unused = AVAILABLE_DISK_SPACE - root.total_size
    need_to_delete = NEEDED_FOR_UPDATE - unused
    return min(size for size in iter_sizes(root) if size >= need_to_delete)


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def test_part_2():
    puzzle_input = read_input("input_test")
    assert part_2(puzzle_input) == EXPECTED_PART_2


def main():
    root = read_input("input")
    print(part_1(root))
    print(part_2(root))


if __name__ == "__main__":
    main()
