import re


DOUBLE_CHARACTER = re.compile(r".*(?P<c>[a-z])(?P=c)")

DOUBLE_PAIR = re.compile(r".*(?P<pair>[a-z][a-z]).*(?P=pair)")
REPEAT_WITH_GAP = re.compile(r".*(?P<c>[a-z])[a-z](?P=c)")


def is_nice_part_one(string):
    return (
        has_three_vowels(string)
        and matches_re(string, DOUBLE_CHARACTER)
        and is_allowed(string)
    )


def has_three_vowels(string):
    return sum(c in "aeiou" for c in string) >= 3


def is_allowed(string):
    return all(substr not in string for substr in ["ab", "cd", "pq", "xy"])


def is_nice_part_two(string):
    return (
        matches_re(string, DOUBLE_PAIR)
        and matches_re(string, REPEAT_WITH_GAP)
    )


def matches_re(string, re):
    return re.match(string) is not None


def main():
    with open("input") as lines:
        print(sum(is_nice_part_one(line.strip()) for line in lines))

    with open("input") as lines:
        print(sum(is_nice_part_two(line.strip()) for line in lines))


if __name__ == '__main__':
    main()
