#!/usr/bin/env python3
import re
from collections import defaultdict


class Reindeer:
    LINE_RE = re.compile(
        r"(?P<name>.*) can fly (?P<speed>\d*) km/s for (?P<fly_duration>\d*) "
        r"seconds, but then must rest for (?P<rest_duration>\d*) seconds."
    )

    def __init__(self, name, speed, fly_duration, rest_duration):
        self.name = name
        self.speed = int(speed)
        self.fly_duration = int(fly_duration)
        self.rest_duration = int(rest_duration)
        self.time_remaining = self.fly_duration
        self.state = "flying"
        self.current_speed = self.speed
        self.position = 0

    @classmethod
    def from_line(cls, line):
        return cls(*cls.LINE_RE.match(line.strip()).groups())

    def simulate_flight(self, time):
        for _ in range(time):
            self.move()
        return self.position

    def move(self):
        if self.time_remaining == 0:
            if self.state == "flying":
                self.state = "resting"
                self.time_remaining = self.rest_duration
                self.current_speed = 0
            else:
                self.state = "flying"
                self.time_remaining = self.fly_duration
                self.current_speed = self.speed
        self.time_remaining -= 1
        self.position += self.current_speed


def score_reindeers(reindeers, time):
    seconds_in_lead = defaultdict(int)
    for _ in range(time):
        for reindeer in reindeers:
            reindeer.move()
        leading = max(reindeers, key=lambda r: r.position)
        for reindeer in reindeers:
            if reindeer.position == leading.position:
                seconds_in_lead[reindeer.name] += 1
    return seconds_in_lead


def read_input(filename):
    with open(filename) as lines:
        return list(map(Reindeer.from_line, lines))


def main():
    time = 2503
    print(max(r.simulate_flight(time) for r in read_input("input")))

    seconds_in_lead = score_reindeers(read_input("input"), time)
    print(max(seconds_in_lead.values()))


if __name__ == '__main__':
    main()
