#!/usr/bin/env python3

def parse_direction(direction):
    return direction[0], int(direction[1:])


def goto(position, heading, distance):
    old_position = tuple(position)
    position[heading % 2] += distance * (1 if heading < 2 else -1)
    if heading % 2:
        return [(position[0], y) for y in range(old_position[1] + 1, position[1] + 1)]
    else:
        return [(x, position[1]) for x in range(old_position[0] + 1, position[0] + 1)]


def main():
    with open("input") as puzzle_input:
        directions = [
            parse_direction(direction)
            for direction in puzzle_input.read().split(", ")
        ]

    position = [0, 0]
    past_positions = []
    heading = 1
    for direction, distance in directions:
        heading = (heading + (1 if direction == "L" else -1)) % 4
        past_positions.extend(goto(position, heading, distance))
    print(sum(map(abs, position)))

    seen = set()
    for position in past_positions:
        if position in seen:
            print(sum(map(abs, position)))
            break
        seen.add(position)


if __name__ == "__main__":
    main()
