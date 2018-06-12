def final_floor(instructions):
    floor = 0
    for cmd in instructions:
        if cmd == "(":
            floor += 1
        elif cmd == ")":
            floor -= 1
    return floor


def enters_basement_after(instructions):
    floor = 0
    for i, cmd in enumerate(instructions, 1):
        if cmd == "(":
            floor += 1
        elif cmd == ")":
            floor -= 1
        if floor < 0:
            return i


def main():
    with open("input") as lines:
        instructions = next(lines)

    print(final_floor(instructions))
    print(enters_basement_after(instructions))


if __name__ == "__main__":
    main()
