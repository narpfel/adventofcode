#!/usr/bin/env python3
import re

import numpy as np

COMMAND_FORMAT = re.compile(r"(.*) (\d*),(\d*) through (\d*),(\d*)")


def turn_on(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] = True


def turn_off(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] = False


def toggle(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] ^= True


def turn_on2(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] += 1


def turn_off2(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] -= 1
    lights[lights < 0] = 0


def toggle2(lights, from_x, from_y, to_x, to_y):
    lights[from_x:to_x + 1, from_y:to_y + 1] += 2


COMMANDS_PART1 = {
    "turn on": turn_on,
    "turn off": turn_off,
    "toggle": toggle,
}

COMMANDS_PART2 = {
    "turn on": turn_on2,
    "turn off": turn_off2,
    "toggle": toggle2,
}


def solve_for(part, dtype):
    lights = np.zeros((1000, 1000), dtype=dtype)
    with open("input") as lines:
        for line in lines:
            match = COMMAND_FORMAT.match(line)
            command = match.group(1)
            part[command](lights, *map(int, match.group(2, 3, 4, 5)))
    return lights.sum()


def main():
    print(solve_for(COMMANDS_PART1, bool))
    print(solve_for(COMMANDS_PART2, int))


if __name__ == "__main__":
    main()
