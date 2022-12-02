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

SCORE_PART_2 = {
    "A X": 3,
    "A Y": 4,
    "A Z": 8,
    "B X": 1,
    "B Y": 5,
    "B Z": 9,
    "C X": 2,
    "C Y": 6,
    "C Z": 7,
}


def main():
    with open("input") as input_file:
        strategy_guide = [line.strip() for line in input_file]

    print(sum(SCORE_PART_1[round] for round in strategy_guide))
    print(sum(SCORE_PART_2[round] for round in strategy_guide))


if __name__ == "__main__":
    main()
