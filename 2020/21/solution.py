#!/usr/bin/env python3

from collections import Counter
from collections import defaultdict
from itertools import chain


def parse_line(line):
    ingredients, _, allergens = line.partition(" (contains ")
    return frozenset(ingredients.split()), frozenset(allergens.rstrip(")").split(", "))


def main():
    allergen_to_ingredients = defaultdict(list)
    ingredient_occurrence_counts = Counter()
    with open("input") as lines:
        for line in lines:
            ingredients, allergens = parse_line(line.strip())
            ingredient_occurrence_counts.update(ingredients)
            for allergen in allergens:
                allergen_to_ingredients[allergen].append(ingredients)

    possible_allergen_ingredients = chain.from_iterable(
        frozenset.intersection(*ingredients) for ingredients in allergen_to_ingredients.values()
    )
    impossible_ingredients = (
        frozenset(ingredient_occurrence_counts).difference(possible_allergen_ingredients)
    )
    print(sum(ingredient_occurrence_counts[ingredient] for ingredient in impossible_ingredients))


if __name__ == "__main__":
    main()
