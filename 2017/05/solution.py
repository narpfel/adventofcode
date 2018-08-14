from itertools import count


def iterate_instructions(instructions, modificator):
    instructions = list(instructions)
    ptr = 0
    allowed_ptrs = range(len(instructions))
    for step in count(1):
        offset = instructions[ptr]
        instructions[ptr] += modificator(offset)
        ptr += offset
        if ptr not in allowed_ptrs:
            return step


def main():
    with open("input") as lines:
        instructions = list(map(int, lines))

    print(iterate_instructions(instructions, lambda _: 1))
    print(iterate_instructions(instructions, lambda x: -1 if x >= 3 else 1))


if __name__ == '__main__':
    main()