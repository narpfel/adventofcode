#!/usr/bin/env pypy3

import math
from collections import defaultdict
from collections import deque
from collections import namedtuple
from itertools import count

EXPECTED_PART_1 = 32000000
EXPECTED_PART_1_2 = 11687500


Module = namedtuple("Module", "name, type, targets")


def parse_module(line):
    sender, targets = line.strip().split(" -> ")
    targets = targets.split(", ")
    if sender.startswith("%"):
        ty = "flipflop"
    elif sender.startswith("&"):
        ty = "conjunction"
    else:
        assert sender == "broadcaster"
        ty = "broadcaster"
    sender = sender.strip("%&")
    return Module(name=sender, type=ty, targets=targets)


def read_input(filename):
    with open(filename) as lines:
        return [parse_module(line) for line in lines]


class FlipFlop:
    def __init__(self, name, targets):
        self.name = name
        self.state = False
        self.targets = targets

    def recv(self, time, sender, pulse):
        if pulse:
            return []
        else:
            self.state = not self.state
            return [(self.name, tgt, self.state) for tgt in self.targets]


class Conjunction:
    def __init__(self, name, inputs, targets):
        self.name = name
        self.inputs = {input: False for input in inputs}
        self.targets = targets
        self.first_true_activation = None
        self.activation_difference = None

    def recv(self, time, sender, pulse):
        self.inputs[sender] = pulse
        output = not all(self.inputs.values())
        if output and self.first_true_activation is None:
            self.first_true_activation = time
        elif output and self.activation_difference is None:
            self.activation_difference = time - self.first_true_activation
        return [(self.name, tgt, output) for tgt in self.targets]


class Broadcaster:
    def __init__(self, name, targets):
        self.name = name
        self.targets = targets

    def recv(self, time, sender, pulse):
        return [(self.name, tgt, pulse) for tgt in self.targets]


def setup_initial_state(modules):
    states = {}

    for mod in modules:
        if mod.type == "flipflop":
            states[mod.name] = FlipFlop(mod.name, mod.targets)
        elif mod.type == "conjunction":
            inputs = [
                m.name
                for m in modules
                if mod.name in m.targets
            ]
            states[mod.name] = Conjunction(mod.name, inputs, mod.targets)
        else:
            assert mod.type == "broadcaster"
            states[mod.name] = Broadcaster(mod.name, mod.targets)

    return states


def simulate_one_button_press(states, sent, time):
    signals = deque([("button", "broadcaster", False)])

    while signals:
        sender, target, signal = signals.popleft()
        sent[signal] += 1
        if target in states:
            signals.extend(states[target].recv(time, sender, signal))


def part_1(modules):
    states = setup_initial_state(modules)
    sent = defaultdict(int)

    for time in range(1000):
        simulate_one_button_press(states, sent, time)

    return math.prod(sent.values())


def part_2(modules):
    states = setup_initial_state(modules)
    sent = defaultdict(int)

    rx_dep, = (module.name for module in modules if "rx" in module.targets)
    rx_dep_deps = [module.name for module in modules if rx_dep in module.targets]

    for time in count(1):
        simulate_one_button_press(states, sent, time)

        if all(states[name].activation_difference is not None for name in rx_dep_deps):
            return math.lcm(*(states[name].activation_difference for name in rx_dep_deps))


def test_part_1():
    puzzle_input = read_input("input_test")
    assert part_1(puzzle_input) == EXPECTED_PART_1
    puzzle_input = read_input("input_test_2")
    assert part_1(puzzle_input) == EXPECTED_PART_1_2


def main():
    modules = read_input("input")
    print(part_1(modules))
    print(part_2(modules))


if __name__ == "__main__":
    main()
