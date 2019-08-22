#include <cstdint>

#include <iostream>
#include <iterator>
#include <list>
#include <vector>


constexpr auto player_count = uint64_t{493};
constexpr auto highest_marble_number = uint64_t{71863};


auto play(uint64_t const player_count, uint64_t const highest_marble_number) -> uint64_t {
    auto scores = std::vector<uint64_t>(player_count, 0);
    auto marbles = std::list<uint64_t>{0};
    auto current_marble = std::begin(marbles);
    for (auto marble = size_t{1}; marble <= highest_marble_number; ++marble) {
        auto const player = (marble - 1) % player_count;
        if (marble % 23) {
            if (current_marble == std::prev(std::end(marbles))) {
                current_marble = marbles.emplace(std::next(std::begin(marbles)), marble);
            }
            else {
                current_marble = marbles.emplace(std::next(current_marble, 2), marble);
            }
        }
        else {
            for (auto i = size_t{0}; i < 7; ++i) {
                if (current_marble == std::begin(marbles)) {
                    current_marble = std::end(marbles);
                }
                std::advance(current_marble, -1);
            }
            scores[player] += marble + *current_marble;
            current_marble++;
            marbles.erase(std::prev(current_marble));
        }
    }
    return *std::max_element(std::begin(scores), std::end(scores));
}


auto main() -> int {
    std::cout << play(player_count, highest_marble_number) << '\n';
    std::cout << play(player_count, highest_marble_number * 100) << '\n';
}
