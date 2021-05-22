#include <cstdint>

#include <algorithm>
#include <array>
#include <tuple>
#include <iostream>
#include <map>
#include <string_view>
#include <unordered_map>
#include <vector>

constexpr auto input = std::array<std::uint64_t, 7>{16, 12, 1, 0, 15, 7, 11};

auto solve(auto const& starting_numbers, std::uint64_t const turn_count) -> std::uint64_t {
    auto number_to_turns = std::vector<std::tuple<std::int32_t, std::int32_t>>(turn_count, std::tuple{-1, -1});
    for (auto i = std::size_t{0}; i < size(starting_numbers); ++i) {
        number_to_turns[starting_numbers[i]] = std::tuple{i, -1};
    }
    auto last_spoken = starting_numbers.back();
    for (auto turn = size(starting_numbers); turn < turn_count; ++turn) {
        auto const& [x, y] = number_to_turns[last_spoken];
        if (y == -1) {
            last_spoken = 0;
        }
        else {
            last_spoken = x - y;
        }
        number_to_turns[last_spoken] = std::tuple{turn, std::get<0>(number_to_turns[last_spoken])};
    }
    return last_spoken;
}

auto main() -> int {
    std::cout << solve(input, 2020) << '\n';
    std::cout << solve(input, 30'000'000) << '\n';
}
