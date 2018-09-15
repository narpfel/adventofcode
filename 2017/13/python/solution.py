#!/usr/bin/env pypy3

from itertools import count


def position(depth, time):
    if not depth:
        return 0

    div, mod = divmod(time, depth - 1)
    if div % 2:
        return depth - 1 - mod
    else:
        return mod


def is_caught(depth, time):
    return not position(depth, time)


def severity(firewall, time):
    return sum(
        (position + time) * depth
        for (position, depth) in firewall.items()
        if is_caught(depth, position + time)
    )


def find_delay(firewall):
    return next(time for time in count() if not severity(firewall, time))


def main():
    with open("input") as lines:
        firewall = dict(map(int, line.split(": ")) for line in lines)

    print(severity(firewall, 0))
    print(find_delay(firewall))


if __name__ == "__main__":
    main()
