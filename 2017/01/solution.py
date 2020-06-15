#!/usr/bin/env python3
from functools import partial
from itertools import cycle
from itertools import islice
from itertools import tee


def pairs(xs, selector):
    xs, ys = tee(xs)
    ys = cycle(ys)
    ys = selector(ys)
    return zip(xs, ys)


def skip(n, xs):
    return islice(xs, n, None)


def main():
    with open("input") as lines:
        line = next(lines).strip()

    for selector in partial(skip, 1), partial(skip, len(line) // 2):
        print(
            sum(
                int(x)
                for (x, y)
                in pairs(line, selector)
                if x == y
            )
        )


if __name__ == '__main__':
    main()
