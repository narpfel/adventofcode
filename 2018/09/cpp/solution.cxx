#include <cstddef>
#include <cstdint>

#include <algorithm>
#include <deque>
#include <ranges>
#include <iostream>
#include <iterator>
#include <list>
#include <vector>


constexpr auto player_count = uint64_t{493};
constexpr auto highest_marble_number = uint64_t{71863};

auto rotate_left(auto& xs, size_t const amount) -> void{
    std::ranges::for_each(
        std::ranges::views::iota(size_t{0}, amount),
        [&](auto const&) {
            auto&& val = std::move(xs.front());
            xs.pop_front();
            xs.emplace_back(std::move(val));
        }
    );
}

auto rotate_right(auto& xs, size_t const amount) -> void {
    std::ranges::for_each(
        std::ranges::views::iota(size_t{0}, amount),
        [&](auto const&) {
            auto&& val = std::move(xs.back());
            xs.pop_back();
            xs.emplace_front(std::move(val));
        }
    );
}

auto play(uint64_t const player_count, uint64_t const highest_marble_number) -> uint64_t {
    auto scores = std::vector<uint64_t>(player_count, 0);
    auto marbles = std::deque<uint64_t>{0};
    for (auto marble = size_t{1}; marble <= highest_marble_number; ++marble) {
        auto const player = (marble - 1) % player_count;
        if (marble % 23) {
            rotate_right(marbles, 2);
            marbles.emplace_back(marble);
        }
        else {
            rotate_left(marbles, 7);
            scores[player] += marble + marbles.back();
            marbles.pop_back();
        }
    }
    return *std::max_element(std::begin(scores), std::end(scores));
}


auto main() -> int {
    std::cout << play(player_count, highest_marble_number) << '\n';
    std::cout << play(player_count, highest_marble_number * 100) << '\n';
}
