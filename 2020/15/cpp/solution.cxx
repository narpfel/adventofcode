#include <cstdint>

#include <array>
#include <iostream>
#include <vector>

constexpr auto input = std::array<std::uint64_t, 7>{16, 12, 1, 0, 15, 7, 11};

auto solve(auto const& starting_numbers, std::uint64_t const turn_count) -> std::uint64_t {
    auto number_to_turn = std::vector<std::int32_t>(turn_count, -1);
    for (auto i = std::size_t{0}; i < size(starting_numbers) - 1; ++i) {
        number_to_turn[starting_numbers[i]] = i;
    }
    auto last_spoken = starting_numbers.back();
    for (auto turn = size(starting_numbers); turn < turn_count; ++turn) {
        auto const last_spoken_on_turn = number_to_turn[last_spoken];
        number_to_turn[last_spoken] = turn - 1;
        if (last_spoken_on_turn == -1) {
            last_spoken = 0;
        }
        else {
            last_spoken = turn - last_spoken_on_turn - 1;
        }
    }
    return last_spoken;
}

auto main() -> int {
    std::cout << solve(input, 2020) << '\n';
    std::cout << solve(input, 30'000'000) << '\n';
}
