#include <cstdint>

#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <span>
#include <string>
#include <utility>
#include <vector>


using Value = std::uint8_t;

auto read_input(std::filesystem::path const &path) {
    auto numbers = std::vector<Value>{};
    auto input_file = std::ifstream{path};
    for (std::string line; std::getline(input_file, line);) {
        numbers.emplace_back(std::stoull(line));
    }
    return numbers;
}

template<typename InputIterator>
auto weight(InputIterator const first, InputIterator const last) {
    return std::accumulate(first, last, uint64_t{0});
}

template<typename InputIterator>
auto calculate_weight_and_quantum_entanglement(
    InputIterator const first,
    InputIterator const last,
    std::span<Value const> const weights
) -> std::pair<uint64_t, uint64_t> {
    auto total_weight = uint64_t{0};
    auto quantum_entanglement = uint64_t{1};
    for (auto it = first; it < last; ++it) {
        auto const weight = uint64_t{weights[*it]};
        total_weight += weight;
        quantum_entanglement *= weight;
    }
    return std::make_pair(total_weight, quantum_entanglement);
}

auto find_best_solution_of_length(
    uint64_t const target_weight,
    std::span<Value const> const weights,
    size_t const r
) {
    auto const n = weights.size();
    auto indices = std::vector<size_t>(r);
    std::iota(std::begin(indices), std::end(indices), 0);
    auto min_quantum_entanglement = std::numeric_limits<uint64_t>::max();

    auto const [w, q] = calculate_weight_and_quantum_entanglement(
        std::begin(indices),
        std::end(indices),
        weights
    );
    if (w == target_weight && min_quantum_entanglement > q) {
        min_quantum_entanglement = q;
    }

    while (true) {
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
        auto j = i + 1;
        while (j < r) {
            indices[j] = indices[j - 1] + 1;
            j += 1;
        }

        auto const [w, q] = calculate_weight_and_quantum_entanglement(
            std::begin(indices),
            std::end(indices),
            weights
        );
        if (w == target_weight && min_quantum_entanglement > q) {
            min_quantum_entanglement = q;
        }
    }
}

auto solve(uint64_t const target_weight, std::span<Value const> const weights) -> uint64_t {
    auto min_quantum_entanglement = std::numeric_limits<uint64_t>::max();
    for (auto r = decltype(weights.size()){1}; r < weights.size(); ++r) {
        auto const q = find_best_solution_of_length(target_weight, weights, r);
        if (q < min_quantum_entanglement) {
            min_quantum_entanglement = q;
        }
    }
    return min_quantum_entanglement;
}

auto main() -> int {
    auto const input = read_input("input");
    auto const part1 = weight(std::begin(input), std::end(input)) / 3;
    auto const part2 = weight(std::begin(input), std::end(input)) / 4;
    std::cout << solve(part1, input) << '\n';
    std::cout << solve(part2, input) << '\n';
}
