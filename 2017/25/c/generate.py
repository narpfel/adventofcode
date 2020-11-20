#!/usr/bin/env python3
import sys

sys.path.append("../python")

from main import parse_input  # noqa: E402 (import from modified `sys.path`)

C_PREAMBLE = """\
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

size_t
// FIXME: `clang` inlines this function everywhere. This makes the assembly
// more readable.
__attribute__((noinline))
sum(char const* const bytes, size_t const size) {{
    size_t count = 0;
    for (size_t i = 0; i < size; ++i) {{
        count += (_Bool)bytes[i];
    }}
    return count;
}}

#define MEMORY_SIZE (2 * {step_count}L + 1)
int main(void) {{
    char* const memory = calloc(MEMORY_SIZE, sizeof(char));
    char* cursor = memory + MEMORY_SIZE / 2;
    size_t step = 0;

    goto state_{initial_state}_on_0;
"""

C_STEP = """\

state_{state.name}_on_{cell_value}:
    if (step == {step_count}) {{
        printf("%" PRIu64 "\\n", sum(memory, MEMORY_SIZE));
        return 0;
    }}
    ++step;
    *cursor = {transition.value};
    cursor += {transition.direction};
    static void* dispatch_state_{state.name}_on_{cell_value}[] = {{
        &&state_{transition.next_state}_on_0,
        &&state_{transition.next_state}_on_1
    }};
    goto *dispatch_state_{state.name}_on_{cell_value}[(size_t)*cursor];
"""

C_POSTAMBLE = """\
}
"""


def generate_c(initial_state, step_count, states):
    print(C_PREAMBLE.format(initial_state=initial_state, step_count=step_count))
    for state in states.values():
        for cell_value, transition in state.transitions.items():
            print(C_STEP.format(
                step_count=step_count,
                cell_value=cell_value,
                state=state,
                transition=transition
            ))
    print(C_POSTAMBLE)


def main():
    initial_state, step_count, states = parse_input("input")
    generate_c(initial_state, step_count, states)


if __name__ == "__main__":
    main()
