#!/usr/bin/env python3

def main():
    with open("input") as lines:
        lines = list(lines)

    print(
        sum(
            len(set(line.split())) == len(line.split())
            for line in lines
        )
    )

    print(
        sum(
            len({
                "".join(sorted(word)) for word in line.split()
            }) == len(line.split())
            for line in lines
        )
    )


if __name__ == "__main__":
    main()
