#!/usr/bin/env pypy3

def parse_input(filename):
    with open(filename) as lines:
        for line in lines:
            yield tuple(map(int, line.split(",")))


def distance(p1, p2):
    return sum(
        abs(a - b)
        for a, b in zip(p1, p2)
    )


def solve(filename):
    points = parse_input(filename)
    constellations = []

    for point in points:
        new_constellation = {point}
        new_constellations = [new_constellation]
        for constellation in constellations:
            if any(distance(point, p) <= 3 for p in constellation):
                new_constellation.update(constellation)
            else:
                new_constellations.append(constellation)
        constellations = new_constellations

    return len(constellations)


def test():
    assert solve("input_test_1") == 2
    assert solve("input_test_2") == 1
    assert solve("input_test_3") == 4
    assert solve("input_test_4") == 3
    assert solve("input_test_5") == 8


def main():
    print(solve("input"))


if __name__ == "__main__":
    main()
