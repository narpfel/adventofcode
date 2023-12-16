#!/usr/bin/env pypy3

EXPECTED_PART_1 = 46


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(contraption, start=((0, 0), (1, 0))):
    beams = [start]
    seen = set()

    while beams:
        beam = (x, y), (Δx, Δy) = beams.pop()
        if beam not in seen and y in range(len(contraption)) and x in range(len(contraption[y])):
            seen.add(beam)
            match contraption[y][x]:
                case ".":
                    beams.append(((x + Δx, y + Δy), (Δx, Δy)))
                case "/":
                    Δx, Δy = -Δy, -Δx
                    beams.append(((x + Δx, y + Δy), (Δx, Δy)))
                case "\\":
                    Δx, Δy = Δy, Δx
                    beams.append(((x + Δx, y + Δy), (Δx, Δy)))
                case "|":
                    if Δy == 0:
                        beams.append(((x, y), (0, -1)))
                        beams.append(((x, y), (0, 1)))
                    else:
                        beams.append(((x + Δx, y + Δy), (Δx, Δy)))
                case "-":
                    if Δx == 0:
                        beams.append(((x, y), (-1, 0)))
                        beams.append(((x, y), (1, 0)))
                    else:
                        beams.append(((x + Δx, y + Δy), (Δx, Δy)))
                case c:
                    assert False, c

    return len({point for point, _ in seen})


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1


def main():
    contraption = read_input("input")
    print(part_1(contraption))


if __name__ == "__main__":
    main()