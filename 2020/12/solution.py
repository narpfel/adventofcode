#!/usr/bin/env python3

import attr
import pytest


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
        else:
            raise ValueError(f"invalid instruction: {instruction!r}")

    def perform_all(self, instructions):
        for instruction in instructions:
            self.perform(instruction)

    @property
    def distance(self):
        return sum(abs(coord) for coord in self.position)


@attr.s
class ShipWithWaypoint:
    waypoint = attr.ib(factory=lambda: Ship([10, 1]))
    ship = attr.ib(factory=Ship)

    def perform(self, instruction):
        if instruction.type in Ship.DIRECTIONS:
            self.waypoint.perform(instruction)
        elif instruction.type == "L":
            if instruction.value % 90:
                raise NotImplementedError("non-90 degree rotations not supported")
            for _ in range(instruction.value // 90):
                self.waypoint.position = [-self.waypoint.position[1], self.waypoint.position[0]]
        elif instruction.type == "R":
            if instruction.value % 90:
                raise NotImplementedError("non-90 degree rotations not supported")
            for _ in range(4 - instruction.value // 90):
                self.waypoint.position = [-self.waypoint.position[1], self.waypoint.position[0]]
        elif instruction.type == "F":
            for _ in range(instruction.value):
                self.ship.position[0] += self.waypoint.position[0]
                self.ship.position[1] += self.waypoint.position[1]

    def perform_all(self, instructions):
        for instruction in instructions:
            self.perform(instruction)

    @property
    def distance(self):
        return self.ship.distance


def read_input(filename):
    with open(filename) as lines:
        return [Instruction.from_str(line) for line in lines]


def solve(ship_type, instructions):
    ship = ship_type()
    ship.perform_all(instructions)
    return ship.distance


@pytest.mark.parametrize("ship_type, expected", [(Ship, 25), (ShipWithWaypoint, 286)])
def test_parts(ship_type, expected):
    assert solve(ship_type, read_input("input_test")) == expected


def main():
    instructions = read_input("input")
    print(solve(Ship, instructions))
    print(solve(ShipWithWaypoint, instructions))


if __name__ == "__main__":
    main()
