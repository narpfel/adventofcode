#!/usr/bin/env python3

from collections import Counter


def main():
    with open("input") as lines:
        messages = [line.strip() for line in lines]

    abundances = [Counter(column) for column in zip(*messages)]

    print(
        "".join(
            abundance.most_common(1)[0][0]
            for abundance in abundances
        )
    )

    print(
        "".join(
            abundance.most_common()[-1][0]
            for abundance in abundances
        )
    )


if __name__ == "__main__":
    main()
