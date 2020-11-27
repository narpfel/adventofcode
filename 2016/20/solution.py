#!/usr/bin/env python3

import bisect


def insert(firewall, ip_range):
    low, high = ip_range
    i = bisect.bisect_left(firewall, low)
    j = bisect.bisect(firewall, high)
    if i % 2 == 0 and j % 2 == 0:
        # start in allowed range, end in allowed range
        firewall[i:j] = [low, high]
    elif i % 2 == 0 and j % 2 != 0:
        # start in allowed range, end in blocked range
        firewall[i:j] = [low]
    elif i % 2 != 0 and j % 2 == 0:
        # start in blocked range, end in allowed range
        firewall[i:j] = [high]
    else:
        # both in blocked ranges
        firewall[i:j] = []


def compactify(firewall):
    last = firewall[-1]
    firewall = iter(firewall)
    yield next(firewall)
    for x, y in zip(firewall, firewall):
        if y != x + 1:
            yield x
            yield y
    yield last


def closed_ip_count(filters):
    filters = iter(filters)
    return sum(high - (low - 1) for low, high in zip(filters, filters))


def main():
    ranges = []
    with open("input") as lines:
        for line in lines:
            low, _, high = line.partition("-")
            ranges.append((int(low), int(high)))

    firewall = []
    for ip_range in ranges:
        insert(firewall, ip_range)
    firewall = list(compactify(firewall))

    if firewall[0] == 0:
        print(firewall[1] + 1)
    else:
        print(0)

    print(2 ** 32 - closed_ip_count(firewall))


if __name__ == "__main__":
    main()
