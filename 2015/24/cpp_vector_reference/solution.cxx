#include <cstdint>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
#include <limits>
#include <numeric>
#include <string>
#include <utility>
#include <vector>


using Value = std::uint8_t;


template<typename InputIterator>
auto weight(InputIterator const first, InputIterator const last) {
    return std::accumulate(first, last, uint64_t{0});
}

auto calculate_weight_and_quantum_entaglement(
    std::vector<size_t> const &indices,
    std::vector<Value> const &weights
) -> std::pair<uint64_t, uint64_t> {
    auto total_weight = uint64_t{0};
    auto quantum_entanglement = uint64_t{1};
    for (auto const index: indices) {
        auto const weight = uint64_t{weights[index]};
        total_weight += weight;
        quantum_entanglement *= weight;
    }
    return std::make_pair(total_weight, quantum_entanglement);
}

auto find_best_solution_of_length(
    uint64_t const target_weight,
    std::vector<Value> const &weights,
    size_t const r
) {
    auto const n = weights.size();
    auto indices = std::vector<size_t>(r);
    std::iota(std::begin(indices), std::end(indices), 0);
    auto min_quantum_entanglement = std::numeric_limits<uint64_t>::max();

    while (true) {
        auto const [w, q] = calculate_weight_and_quantum_entaglement(indices, weights);
        if (w == target_weight && min_quantum_entanglement > q) {
            min_quantum_entanglement = q;
        }

        auto i = r - 1;

        while (indices[i] == i + n - r) {
            if (i > 0) {
                i -= 1;
            }
            else {
                return min_quantum_entanglement;
            }
        }

        indices[i] += 1;
        for (auto j = i + 1; j < r; ++j) {
            indices[j] = indices[j - 1] + 1;
        }
    }
}

auto solve(uint64_t const target_weight, std::vector<Value> const &weights) -> uint64_t {
    auto min_quantum_entanglement = std::numeric_limits<uint64_t>::max();
    for (auto r = size_t{1}; r < weights.size(); ++r) {
        auto const q = find_best_solution_of_length(target_weight, weights, r);
        if (q < min_quantum_entanglement) {
            min_quantum_entanglement = q;
        }
    }
    return min_quantum_entanglement;
}

auto read_input(std::filesystem::path const &path) {
    auto numbers = std::vector<Value>{};
    auto input_file = std::ifstream{path};
    std::copy(
        std::istream_iterator<uint64_t>{input_file},
        std::istream_iterator<uint64_t>{},
        std::back_inserter(numbers)
    );
    return numbers;
}


auto main() -> int {
    auto const input = read_input("input");
    auto const part1 = weight(std::begin(input), std::end(input)) / 3;
    auto const part2 = weight(std::begin(input), std::end(input)) / 4;
    std::cout << solve(part1, input) << '\n';
    std::cout << solve(part2, input) << '\n';
}
