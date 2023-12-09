#!/usr/bin/env python3

from collections import deque
from collections import namedtuple

EXPECTED_PART_1 = 35
EXPECTED_PART_2 = 46


class Range(namedtuple("Range", "dest, src, len")):
    __slots__ = ()

    @property
    def start(self):
        return self.src

    @property
    def stop(self):
        return self.src + self.len

    def apply_to_range(self, other):
        if self.stop < other.start:
            return (None, None, other)
        if other.stop < self.start:
            return (other, None, None)
        if self.start >= other.start and self.stop <= other.stop:
            overlap_start = self.dest + max(self.start, other.start) - self.src
            overlap_end = self.dest + min(self.stop, other.stop) - self.src
            return (
                range(other.start, self.start),
                range(self.dest, self.dest + self.len),
                range(self.stop, other.stop),
            )
        if other.start >= self.start and other.stop <= self.stop:
            overlap_start = self.dest + other.start - self.src
            return (
                None,
                range(overlap_start, overlap_start + len(other)),
                None,
            )
        if self.start < other.start and self.stop < other.stop:
            overlap_start = self.dest + other.start - self.src
            overlap_end = self.dest + self.len
            return (
                None,
                range(overlap_start, overlap_end),
                range(self.stop, other.stop),
            )
        if other.start < self.start and other.stop < self.stop:
            overlap_start = self.dest
            overlap_end = self.dest + other.stop - self.src
            return (
                range(other.start, self.start),
                range(overlap_start, overlap_end),
                None,
            )

        assert False, "unreachable"

    def __repr__(self):
        return f"<{range(self.start, self.stop)} {self.dest - self.src:+}>"


def read_input(filename):
    with open(filename) as lines:
        blocks = lines.read().split("\n\n")

    seeds = [int(x) for x in blocks[0].split(":")[-1].split()]
    maps = {}
    for block in blocks[1:]:
        lines = block.splitlines()
        from_, to = tuple(lines[0].split()[0].split("-to-"))
        ranges = [
            Range(*map(int, line.split()))
            for line in lines[1:]
        ]
        maps[from_, to] = ranges
    return seeds, maps


def part_1(seeds, maps):
    locations = []
    for seed in seeds:
        for map_ in maps.values():
            for range_ in map_:
                if seed in range(range_.src, range_.src + range_.len):
                    seed = seed - range_.src + range_.dest
                    break
        locations.append(seed)

    return min(locations)


def compress(ranges):
    ranges = iter(ranges)
    rng = next(ranges)
    for other in ranges:
        if other.start == rng.start:
            rng = other
        elif other.start == rng.stop:
            rng = range(rng.start, other.stop)
        else:
            yield rng
            rng = other
    yield rng


def chunked(xs, chunksize):
    xs = iter(xs)
    try:
        while True:
            chunk = []
            for _ in range(chunksize):
                chunk.append(next(xs))
            yield chunk
    except StopIteration:
        if chunk:
            yield chunk


def part_2(seeds, maps):
    ranges = [range(start, start + len) for start, len in chunked(seeds, 2)]
    for map_ in maps.values():
        new_ranges = []
        srcs = deque(ranges)
        seen = set()
        while srcs:
            src = srcs.popleft()
            if src not in seen:
                seen.add(src)
                for dest in map_:
                    (before, overlap, after) = dest.apply_to_range(src)
                    assert len(before or ()) + len(overlap or ()) + len(after or ()) == len(src)
                    if before:
                        srcs.append(before)
                    if after:
                        srcs.append(after)
                    if overlap:
                        new_ranges.append(overlap)
                        break
                else:
                    new_ranges.append(src)

        ranges = compress(
            sorted(
                (range_ for range_ in set(new_ranges) if range_),
                key=lambda r: (r.start, r.stop),
            ),
        )
    return min(range_.start for range_ in ranges)


def test_part_1():
    seeds, maps = read_input("input_test")
    assert part_1(seeds, maps) == EXPECTED_PART_1


def test_part_2():
    seeds, maps = read_input("input_test")
    assert part_2(seeds, maps) == EXPECTED_PART_2


def main():
    seeds, maps = read_input("input")
    print(part_1(seeds, maps))
    print(part_2(seeds, maps))


if __name__ == "__main__":
    main()
