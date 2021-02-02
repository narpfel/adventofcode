#!/usr/bin/env python3

from collections import Counter
from collections import defaultdict
from functools import partial
from itertools import chain
from operator import getitem


def parse_line(line):
    ingredients, _, allergens = line.partition(" (contains ")
    return frozenset(ingredients.split()), frozenset(allergens.rstrip(")").split(", "))


def map_ingredients_to_allergens(
    allergens,
    allergen_to_possible_ingredients,
    ingredients_to_allergens=None,
    i=0,
):
    if ingredients_to_allergens is None:
        ingredients_to_allergens = {}

    if i == len(allergens):
        return ingredients_to_allergens

    for possible_ingredient in allergen_to_possible_ingredients[allergens[i]]:
        if possible_ingredient not in ingredients_to_allergens:
            solution = map_ingredients_to_allergens(
                allergens,
                allergen_to_possible_ingredients,
                {**ingredients_to_allergens, possible_ingredient: allergens[i]},
                i + 1,
            )
            if solution is not None:
                return solution
    return None


def main():
    allergen_to_ingredients = defaultdict(list)
    ingredient_occurrence_counts = Counter()
    with open("input") as lines:
        for line in lines:
            ingredients, allergens = parse_line(line.strip())
            ingredient_occurrence_counts.update(ingredients)
            for allergen in allergens:
                allergen_to_ingredients[allergen].append(ingredients)

    possible_allergen_ingredients = frozenset(
        chain.from_iterable(
            frozenset.intersection(*ingredients)
            for ingredients in allergen_to_ingredients.values()
        ),
    )
    impossible_ingredients = (
        frozenset(ingredient_occurrence_counts) - possible_allergen_ingredients
    )
    print(sum(ingredient_occurrence_counts[ingredient] for ingredient in impossible_ingredients))

    allergen_to_possible_ingredients = {
        allergen: possible_allergen_ingredients.intersection(*ingredients) - impossible_ingredients
        for allergen, ingredients in allergen_to_ingredients.items()
    }

    ingredients_to_allergens = map_ingredients_to_allergens(
        allergens=sorted(allergen_to_ingredients),
        allergen_to_possible_ingredients=allergen_to_possible_ingredients,
    )

    print(
        ",".join(
            sorted(possible_allergen_ingredients, key=partial(getitem, ingredients_to_allergens)),
        ),
    )


if __name__ == "__main__":
    main()
