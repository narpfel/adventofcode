from collections import defaultdict


def make_santa(gifts):
    x, y = 0, 0

    def decode_move(direction):
        nonlocal x, y
        if direction == "^":
            y += 1
        elif direction == "v":
            y -= 1
        elif direction == "<":
            x -= 1
        elif direction == ">":
            x += 1
        gifts[(x, y)] += 1

    return decode_move


def main():
    with open("input") as lines:
        directions = next(lines)

    x, y = 0, 0
    gifts = defaultdict(int)
    gifts[(x, y)] += 1

    santa = make_santa(gifts)
    robo_santa = make_santa(gifts)

    directions = iter(directions)
    for santa_direction, robo_direction in zip(directions, directions):
        santa(santa_direction)
        robo_santa(robo_direction)
    print(len(gifts))


if __name__ == '__main__':
    main()
