#!/usr/bin/env python3

import attr


@attr.s
class Instruction:
    type = attr.ib()
    value = attr.ib(converter=int)

    @classmethod
    def from_str(cls, s):
        return cls(s[:1], s[1:])


@attr.s
class Ship:
    DIRECTIONS = "ESWN"
    position = attr.ib(factory=lambda: [0, 0])
    direction = attr.ib(default=0)

    def perform(self, instruction):
        if instruction.type == "N":
            self.position[1] += instruction.value
        elif instruction.type == "E":
            self.position[0] += instruction.value
        elif instruction.type == "S":
            self.position[1] -= instruction.value
        elif instruction.type == "W":
            self.position[0] -= instruction.value
        elif instruction.type == "L":
            if instruction.value % 90:
                raise NotImplementedError("non-90 degree rotations not supported")
            self.direction = (self.direction - instruction.value // 90) % len(self.DIRECTIONS)
        elif instruction.type == "R":
            if instruction.value % 90:
                raise NotImplementedError("non-90 degree rotations not supported")
            self.direction = (self.direction + instruction.value // 90) % len(self.DIRECTIONS)
        elif instruction.type == "F":
            self.perform(Instruction(self.DIRECTIONS[self.direction], instruction.value))

    def perform_all(self, instructions):
        for instruction in instructions:
            self.perform(instruction)

    @property
    def distance(self):
        return sum(abs(coord) for coord in self.position)


def read_input(filename):
    with open(filename) as lines:
        return [Instruction.from_str(line) for line in lines]


def test_part1():
    ship = Ship()
    ship.perform_all(read_input("input_test"))
    assert ship.distance == 25


def main():
    instructions = read_input("input")
    ship = Ship()
    ship.perform_all(instructions)
    print(ship.distance)


if __name__ == "__main__":
    main()
