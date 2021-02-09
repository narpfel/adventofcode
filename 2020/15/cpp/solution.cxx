#include <cstdint>

#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <string_view>
#include <unordered_map>
#include <vector>

constexpr auto input = std::array<std::uint64_t, 7>{16, 12, 1, 0, 15, 7, 11};

auto solve(auto const& starting_numbers, std::uint64_t const turn_count) -> std::uint64_t {
    auto number_to_turns = std::unordered_map<std::uint64_t, std::vector<std::uint64_t>>{};
    std::generate_n(
        std::inserter(number_to_turns, begin(number_to_turns)),
        size(starting_numbers),
        [&, n=std::uint64_t{0}]() mutable {
            auto const result = std::pair{starting_numbers[n], std::vector{n}};
            ++n;
            return result;
        }
    );
    auto last_spoken = starting_numbers.back();
    for (auto turn = size(starting_numbers); turn < turn_count; ++turn) {
        auto const& spoken_on = number_to_turns[last_spoken];
        if (size(spoken_on) == 1) {
            last_spoken = 0;
        }
        else {
            last_spoken = spoken_on.back() - spoken_on[size(spoken_on) - 2];
        }
        number_to_turns[last_spoken].push_back(turn);
    }
    return last_spoken;
}

auto main() -> int {
    std::cout << solve(input, 2020) << '\n';
    std::cout << solve(input, 30'000'000) << '\n';
}
