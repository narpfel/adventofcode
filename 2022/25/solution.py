#!/usr/bin/env python3

EXPECTED_PART_1 = "2=-1=0"

SNAFU_DIGIT_VALUES = {"2": 2, "1": 1, "0": 0, "-": -1, "=": -2}
DIGIT_VALUE_TO_SNAFU = {snafu_digit: value for value, snafu_digit in SNAFU_DIGIT_VALUES.items()}


def read_input(filename):
    with open(filename) as lines:
        return [line.strip() for line in lines]


def part_1(snafu_numbers):
    fuel_requirement = sum(
        SNAFU_DIGIT_VALUES[digit] * 5 ** i
        for number in snafu_numbers
        for i, digit in enumerate(reversed(number))
    )

    snafu_digits = []
    while fuel_requirement:
        fuel_requirement, digit = divmod(fuel_requirement, 5)
        if digit >= 3:
            digit -= 5
            fuel_requirement += 1
        snafu_digits.append(DIGIT_VALUE_TO_SNAFU[digit])

    return "".join(reversed(snafu_digits))


def test_part_1():
    assert part_1(read_input("input_test")) == EXPECTED_PART_1


def main():
    print(part_1(read_input("input")))


if __name__ == "__main__":
    main()
