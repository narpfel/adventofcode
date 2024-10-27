#!/usr/bin/env python3
import re
from itertools import chain
from itertools import groupby
from operator import itemgetter
from textwrap import dedent

REPLACEMENT = re.compile(
    r"(?P<element>[A-Z]?[a-z]?) => (?P<replacement>[A-Za-z]*)",
)
ELEMENT = re.compile(r"([A-Z][a-z]|[A-Z]|[a-z])")


def next_block(file):
    return iter(file.readline, "\n")


def parse_replacement_line(line):
    match = REPLACEMENT.match(line)
    if match is None:
        raise ValueError(f"Not a valid replacement spec: `{line!r}`")
    return match.group("element", "replacement")


def read_replacements(lines):
    for line in lines:
        yield parse_replacement_line(line)


def tokenize(molecule):
    return ELEMENT.findall(molecule)


def replace_first(element, replacement, molecule):
    for i, current in enumerate(molecule):
        if current == element:
            molecule[i] = replacement
            return i
    raise ValueError("no element")


def possible_with_1_replacement(origin, replacements):
    seen = set()
    for element in replacements:
        for replacement in replacements[element]:
            i = 0
            while 0 <= i < len(origin):
                head, tail = origin[:i], origin[i:]
                try:
                    i += replace_first(element, replacement, tail) + 1
                except ValueError:
                    break
                seen.add("".join(head + tail))
    return seen


def endpoints(replacements):
    return set(
        tokenize("".join(chain.from_iterable(replacements.values()))),
    ) - set(replacements)


def steps(result):
    Rn = result.count("Rn")
    Y = result.count("Y")
    return len(result) - 1 - (Rn - Y) * 2 - Y * 4


def main():
    with open("input") as lines:
        replacements = {
            key: {replacement for _, replacement in group}
            for key, group in groupby(
                read_replacements(next_block(lines)),
                key=itemgetter(0),
            )
        }
        medicine = tokenize(next(lines))

    print(f"len(medicine) = {len(medicine)}")
    print()
    print(
        "Solution (part 1):",
        len(possible_with_1_replacement(medicine, replacements)),
    )
    print()
    print("endpoints")
    for endpoint in endpoints(replacements):
        print(f"{endpoint}: {medicine.count(endpoint)}")

    print(
        dedent(
            """
                Solution (part 2): {0}
                ----------------------

                EBNF for constructing molecules:
                molecule ::= element*;
                element ::= (element element)
                          | (element "Rn" element ("Y" element)? "Ar");

                Hence, each step increases the number of elements in the molecule by
                either 1 or 3 or 5. Iff the length is increased by 5, then one "Y", one
                "Rn" and one "Ar" is added; iff the length is increased by 3, one "Rn"
                and one "Ar" are added. There are no "C"’s in the resulting medicine so
                adding two "Y"’s in one step is not possible. The minimum number of
                steps therefore is `len(medicine)` - 1 [the "e" the reaction is
                started with] - 2 * ([number of "Rn"’s] - [number of "Y"’s]) - 4 *
                [number of "Y"’s] == {0}.

                Note (2017-12-06): This solution also works for solutions containing
                productions that produce multiple "Y"’s because each "Y" adds exactly
                two elements to the molecule. The correct EBNF is
                molecule ::= element*;
                element ::= (element element)
                          | (element "Rn" element ("Y" element)* "Ar");
            """.format(steps(medicine)),
        ),
    )


if __name__ == "__main__":
    main()
