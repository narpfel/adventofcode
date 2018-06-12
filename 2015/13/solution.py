from functools import partial
from itertools import permutations, tee
import re


def read_input(filename):
    line_format = re.compile(
        r"(?P<name>.*) would (?P<gain_or_lose>.*) (?P<happiness>\d*) happiness "
        r"units by sitting next to (?P<other>.*)\."
    )
    with open(filename) as input:
        for line in input:
            match = line_format.match(line.strip())
            yield (
                (match.group("name"), match.group("other")),
                int(match.group("happiness")) * (-1 if match.group("gain_or_lose") == "lose" else 1)
            )


def sum_happiness(pairs, pair2happiness):
    return sum(
        pair2happiness[pair] + pair2happiness[tuple(reversed(pair))]
        for pair in pairs
    )


def pairs(arrangement):
    yield arrangement[-1], arrangement[0]
    a, b = tee(iter(arrangement))
    next(b, None)
    yield from zip(a, b)


def happiness(arrangement, pair2happiness):
    return sum_happiness(pairs(arrangement), pair2happiness)


def find_best_arrangement(people, pair2happiness):
    return max(
        permutations(people),
        key=partial(happiness, pair2happiness=pair2happiness)
    )


def main():
    pair2happiness = dict(read_input("input"))
    people = set(pair[0] for pair in pair2happiness)
    best_arrangement = find_best_arrangement(people, pair2happiness)
    print(happiness(best_arrangement, pair2happiness))

    for person in people:
        pair2happiness[("me", person)] = 0
        pair2happiness[(person, "me")] = 0
    people.add("me")

    best_arrangement = find_best_arrangement(people, pair2happiness)
    print(happiness(best_arrangement, pair2happiness))


if __name__ == '__main__':
    main()
