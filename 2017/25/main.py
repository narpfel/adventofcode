#!/usr/bin/env pypy3
import re
from collections import defaultdict

import attr

PREAMBLE_RE = re.compile(
    r"""Begin in state (?P<initial_state>.)\.
Perform a diagnostic checksum after (?P<step_count>\d+) steps\."""
)

STATES_RE = re.compile(
    r"""In state (?P<state_name>.):
  If the current value is 0:
    - Write the value (?P<on_0_value>[01])\.
    - Move one slot to the (?P<on_0_direction>left|right)\.
    - Continue with state (?P<on_0_state>.)\.
  If the current value is 1:
    - Write the value (?P<on_1_value>[01])\.
    - Move one slot to the (?P<on_1_direction>left|right)\.
    - Continue with state (?P<on_1_state>.)\.""",
)


@attr.s
class Transition:
    value = attr.ib(converter=int)
    direction = attr.ib(converter=lambda direction: -1 if direction == "left" else 1)
    next_state = attr.ib()


@attr.s
class State:
    name = attr.ib()
    transitions = attr.ib(
        converter=lambda d: {
            state: Transition(
                *(d[f"on_{state}_{value}"] for value in ("value", "direction", "state"))
            )
            for state in (0, 1)
        }
    )


def main():
    with open("input") as input_file:
        preamble, _, states_description = input_file.read().partition("\n\n")

    m = PREAMBLE_RE.match(preamble)
    if m is not None:
        initial_state = m["initial_state"]
        step_count = int(m["step_count"])
    states = {
        m["state_name"]: State(m["state_name"], m.groupdict())
        for m in STATES_RE.finditer(states_description)
    }

    memory = defaultdict(int)
    cursor = 0
    state = initial_state

    for _ in range(step_count):
        transition = states[state].transitions[memory[cursor]]
        memory[cursor] = transition.value
        cursor += transition.direction
        state = transition.next_state

    print(sum(memory.values()))


if __name__ == "__main__":
    main()
