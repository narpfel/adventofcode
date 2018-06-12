from operator import and_, or_, lshift, rshift, invert
from functools import partial
import re
from functools import lru_cache


class Wire:
    def __init__(self, name, input):
        self.name = name
        self.input = input
        self.seen = False

    @lru_cache(2**10)
    def __int__(self):
        try:
            return int(self.input)
        except TypeError:
            return self.input()

    def __call__(self):
        return int(self)


def logic_function(operator, x, y):
    return operator(int(x), int(y)) & 0xFFFF


def logic_function_unary(operator, x):
    return operator(int(x)) & 0xFFFF


LOGIC_FUNCTIONS = {
    "AND": partial(logic_function, and_),
    "OR": partial(logic_function, or_),
    "LSHIFT": partial(logic_function, lshift),
    "RSHIFT": partial(logic_function, rshift),
    "NOT": partial(logic_function_unary, invert),
}

INSTRUCTION = re.compile(
    r"""(
        ((?P<left>\w*)\ (?P<binop>\w*)\ (?P<right>\w*))
        |((?P<operator>\w*)\ (?P<operand>\w*))
        |(?P<single>\w*)
    )\ ->\ (?P<destination>\w*)""",
    re.VERBOSE
)

WIRE_NAME = re.compile(r"[a-z]+")


def main():
    wires = {}
    with open("input") as lines:
        instructions = lines.read()

    for name in WIRE_NAME.findall(instructions):
        wires[name] = Wire(name, None)

    for line in instructions.splitlines():
        match = INSTRUCTION.match(line)
        groups = match.groupdict()
        destination = groups["destination"]
        if groups["binop"] is not None:
            input = partial(
                LOGIC_FUNCTIONS[groups["binop"]],
                wires.get(groups["left"], groups["left"]),
                wires.get(groups["right"], groups["right"])
            )
        elif groups["operator"] is not None:
            input = partial(
                LOGIC_FUNCTIONS[groups["operator"]],
                wires.get(groups["operand"], groups["operand"])
            )
        else:
            input = wires.get(groups["single"], groups["single"])
        wires[destination].input = input

    print(wires["a"]())

    wires["b"].input = wires["a"]()
    Wire.__int__.cache_clear()
    print(wires["a"]())


if __name__ == '__main__':
    main()
