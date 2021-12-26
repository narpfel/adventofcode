// For `getline`
#define _GNU_SOURCE

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <inttypes.h>


typedef uint8_t Value;

struct Pair {
    uint64_t weight;
    uint64_t quantum_entanglement;
};

struct ValueSpan {
    Value* data;
    size_t length;
};

struct IndexSpan {
    size_t* data;
    size_t length;
};

struct IndexSpan index_span_new(size_t const length) {
    struct IndexSpan span = {
        .length = length,
        .data = malloc(length * sizeof(size_t))
    };
    for (size_t i = 0; i < length; ++i) {
        span.data[i] = i;
    }
    return span;
}

void index_span_delete(struct IndexSpan const span) {
    free(span.data);
}

uint64_t weight(struct ValueSpan const values) {
    uint64_t result = 0;
    for (size_t i = 0; i < values.length; ++i) {
        result += values.data[i];
    }
    return result;
}

struct Pair calculate_weight_and_quantum_entanglement(
    struct IndexSpan const indices,
    struct ValueSpan const weights
) {
    uint64_t total_weight = 0;
    uint64_t quantum_entanglement = 1;
    for (size_t i = 0; i < indices.length; ++i) {
        uint64_t const weight = weights.data[indices.data[i]];
        total_weight += weight;
        quantum_entanglement *= weight;
    }
    struct Pair const result = {
        .weight = total_weight,
        .quantum_entanglement = quantum_entanglement
    };
    return result;
}

uint64_t find_best_solution_of_length(
    uint64_t const target_weight,
    struct ValueSpan const weights,
    size_t const length
) {
    size_t const n = weights.length;
    struct IndexSpan indices = index_span_new(length);
    uint64_t min_quantum_entanglement = UINT64_MAX;

    while (true) {
        struct Pair const result = calculate_weight_and_quantum_entanglement(indices, weights);
        if (result.weight == target_weight && min_quantum_entanglement > result.quantum_entanglement) {
            min_quantum_entanglement = result.quantum_entanglement;
        }

        size_t i = length - 1;

        while (indices.data[i] == i + n - length) {
            if (i > 0) {
                i -= 1;
            }
            else {
                index_span_delete(indices);
                return min_quantum_entanglement;
            }
        }
        indices.data[i] += 1;
        for (size_t j = i + 1; j < length; ++j) {
            indices.data[j] = indices.data[j - 1] + 1;
        }
    }
}

uint64_t solve(uint64_t const target_weight, struct ValueSpan const weights) {
    uint64_t min_quantum_entanglement = UINT64_MAX;
    for (size_t length = 1; length < weights.length; ++length) {
        uint64_t const q = find_best_solution_of_length(target_weight, weights, length);
        if (q < min_quantum_entanglement) {
            min_quantum_entanglement = q;
        }
    }
    return min_quantum_entanglement;
}

struct ValueSpan read_input(char const *const filename) {
    FILE *f = fopen(filename, "r");
    if (!f) {
        puts("Unable to read input: no file");
        exit(1);
    }
    char *line = NULL;
    size_t buffer_size = 0;
    struct ValueSpan values = {
        .data = malloc(0),
        .length = 0
    };
    while (getline(&line, &buffer_size, f) != -1) {
        values.data = realloc(values.data, ++values.length);
        values.data[values.length - 1] = atoi(line);
    }
    free(line);
    return values;
}


int main() {
    struct ValueSpan const input = read_input("input");

    uint64_t const part1 = weight(input) / 3;
    uint64_t const part2 = weight(input) / 4;
    printf("%" PRIu64 "\n", solve(part1, input));
    printf("%" PRIu64 "\n", solve(part2, input));

    free(input.data);
    return 0;
}
