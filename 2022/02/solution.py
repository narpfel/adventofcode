#!/usr/bin/env python3

SCORE_PART_1 = {
    "A X": 4,
    "A Y": 8,
    "A Z": 3,
    "B X": 1,
    "B Y": 5,
    "B Z": 9,
    "C X": 7,
    "C Y": 2,
    "C Z": 6,
}


def main():
    with open("input") as input_file:
        strategy_guide = [line.strip() for line in input_file]

    print(sum(SCORE_PART_1[round] for round in strategy_guide))


if __name__ == "__main__":
    main()
