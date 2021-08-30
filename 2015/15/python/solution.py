#!/usr/bin/env pypy3
import re
from operator import mul

INGREDIENT_RE = re.compile(r"""(?x)
    \w+:
    \ capacity\ (?P<capacity>-?\d+),
    \ durability\ (?P<durability>-?\d+),
    \ flavor\ (?P<flavor>-?\d+),
    \ texture\ (?P<texture>-?\d+),
    \ calories\ (?P<calories>\d+)
""")


def score(amount_per_ingredient, transposed_ingredients):
    result = 1
    for property in transposed_ingredients:
        result *= max(0, sum(map(mul, amount_per_ingredient, property)))
    return result


def possible_combinations(n, ingredients):
    # generate code because this is 13x faster than `itertools.product`
    names = [f"_{i}" for i in range(len(ingredients))]
    code = f"""(
        [{", ".join(names)}]
        {" ".join(f"for {name} in range({n})" for name in names)}
        if {" + ".join(names)} == 100
    )"""
    amounts = eval(code, {}, {})

    transposed_ingredients = list(zip(*ingredients))
    return [
        (amount_per_ingredient, score(amount_per_ingredient, transposed_ingredients))
        for amount_per_ingredient in amounts
    ]


def part1(combinations):
    return max(score for _, score in combinations)


def part2(combinations, calories_per_ingredient):
    return max(
        score
        for amounts, score in combinations
        if sum(map(mul, amounts, calories_per_ingredient)) == 500
    )


def parse_input(filename):
    with open(filename) as lines:
        for line in lines:
            match = INGREDIENT_RE.match(line)
            yield (
                (
                    int(match["capacity"]),
                    int(match["durability"]),
                    int(match["flavor"]),
                    int(match["texture"]),
                ),
                int(match["calories"]),
            )


def main():
    ingredients, calories_per_ingredient = zip(*parse_input("input"))
    combinations = possible_combinations(100, ingredients)
    print(part1(combinations))
    print(part2(combinations, calories_per_ingredient))


if __name__ == "__main__":
    main()
