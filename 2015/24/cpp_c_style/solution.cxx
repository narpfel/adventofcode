#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <numeric>
#include <utility>
#include <vector>


using Value = uint8_t;

template<typename T>
struct Span {
    T* data;
    size_t length;

    Span(std::vector<T> &values) : data{values.data()}, length{values.size()} {}
};


uint64_t weight(Span<Value> const values) {
    uint64_t result = 0;
    for (size_t i = 0; i < values.length; ++i) {
        result += values.data[i];
    }
    return result;
}

auto calculate_weight_and_quantum_entanglement(
    Span<size_t> const indices,
    Span<Value> const weights
) {
    uint64_t total_weight = 0;
    uint64_t quantum_entanglement = 1;
    for (size_t i = 0; i < indices.length; ++i) {
        uint64_t const weight = weights.data[indices.data[i]];
        total_weight += weight;
        quantum_entanglement *= weight;
    }
    return std::make_pair(total_weight, quantum_entanglement);
}

uint64_t find_best_solution_of_length(
    uint64_t const target_weight,
    Span<Value> const weights,
    size_t const length
) {
    size_t const n = weights.length;

    auto indices_vector = std::vector<size_t>(length);
    std::iota(std::begin(indices_vector), std::end(indices_vector), 0);
    auto indices = Span<size_t>{indices_vector};
    uint64_t min_quantum_entanglement = UINT64_MAX;

    while (true) {
        auto const [w, q] = calculate_weight_and_quantum_entanglement(indices, weights);
        if (w == target_weight && min_quantum_entanglement > q) {
            min_quantum_entanglement = q;
        }

        size_t i = length - 1;

        while (indices.data[i] == i + n - length) {
            if (i > 0) {
                i -= 1;
            }
            else {
                return min_quantum_entanglement;
            }
        }
        indices.data[i] += 1;
        size_t j = i + 1;
        while (j < length) {
            indices.data[j] = indices.data[j - 1] + 1;
            j += 1;
        }
    }
}

uint64_t solve(uint64_t const target_weight, Span<Value> const weights) {
    uint64_t min_quantum_entanglement = UINT64_MAX;
    for (size_t length = 1; length < weights.length; ++length) {
        uint64_t const q = find_best_solution_of_length(target_weight, weights, length);
        if (q < min_quantum_entanglement) {
            min_quantum_entanglement = q;
        }
    }
    return min_quantum_entanglement;
}

std::vector<Value> read_input(std::filesystem::path const &path) {
    auto numbers = std::vector<Value>{};
    auto input_file = std::ifstream{path};
    std::copy(
        std::istream_iterator<uint64_t>{input_file},
        std::istream_iterator<uint64_t>{},
        std::back_inserter(numbers)
    );
    return numbers;
}


int main() {
    auto input_vector = read_input("input");
    auto const input = Span<Value>{ input_vector };

    uint64_t const part1 = weight(input) / 3;
    uint64_t const part2 = weight(input) / 4;
    printf("%" PRIu64 "\n", solve(part1, input));
    printf("%" PRIu64 "\n", solve(part2, input));

    return 0;
}
