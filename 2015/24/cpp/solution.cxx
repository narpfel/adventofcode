#include <cstdint>

#include <algorithm>
#include <ranges>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iterator>
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
    std::copy(
        std::istream_iterator<uint64_t>{input_file},
        std::istream_iterator<uint64_t>{},
        std::back_inserter(numbers)
    );
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
    size_t const length
) {
    auto const n = weights.size();
    auto indices = std::vector<size_t>(length);
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
        auto i = length - 1;

        while (indices[i] == i + n - length) {
            if (i > 0) {
                i -= 1;
            }
            else {
                return min_quantum_entanglement;
            }
        }
        indices[i] += 1;
        auto j = i + 1;
        while (j < length) {
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
    return std::ranges::min(
        std::ranges::views::iota(1uz, std::ranges::size(weights))
            | std::ranges::views::transform([&](auto const length) {
                return find_best_solution_of_length(target_weight, weights, length);
            })
    );
}


auto main() -> int {
    auto const input = read_input("input");
    auto const part1 = weight(std::begin(input), std::end(input)) / 3;
    auto const part2 = weight(std::begin(input), std::end(input)) / 4;
    std::cout << solve(part1, input) << '\n';
    std::cout << solve(part2, input) << '\n';
}
