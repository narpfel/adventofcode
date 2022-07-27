#include <cstdint>
#include <cstddef>

#include <algorithm>
#include <array>
#include <iostream>
#include <utility>

#include <range/v3/numeric/accumulate.hpp>
#include <range/v3/view/chunk.hpp>
#include <range/v3/view/cycle.hpp>
#include <range/v3/view/enumerate.hpp>
#include <range/v3/view/iota.hpp>
#include <range/v3/view/transform.hpp>


constexpr auto dice = std::to_array<std::pair<std::uint64_t, std::uint64_t>>({
    {3, 1},
    {4, 3},
    {5, 6},
    {6, 7},
    {7, 6},
    {8, 3},
    {9, 1},
});

struct Player {
    std::uint64_t name;
    std::uint64_t position;
    std::uint64_t score;

    auto roll(std::uint64_t const roll) -> void {
        this->position = (this->position + roll) % 10;
        this->score += this->position + 1;
    }
};

auto part_1(auto&& players) -> std::uint64_t {
    auto sides = ranges::views::iota(std::uint64_t{1}, std::uint64_t{101});
    auto die = sides | ranges::views::cycle;
    auto rolls = die
        | ranges::views::chunk(3)
        | ranges::views::transform(
            [](auto const& r) { return ranges::accumulate(r, std::uint64_t{0}); }
        );
    for (auto const& [i, roll]: rolls | ranges::views::enumerate) {
        auto& player = players[static_cast<std::size_t>(i) % 2];
        player.roll(roll);
        if (player.score >= 1000) {
            return (static_cast<std::uint64_t>(i) + 1) * 3 * players[(player.name + 1) % 2].score;
        }
    }
    std::unreachable();
}

auto part_2(
    std::uint64_t const p1, std::uint64_t const p2,
    std::uint64_t const s1, std::uint64_t const s2
) -> std::pair<std::uint64_t, std::uint64_t> {
    auto wins1 = std::uint64_t{0};
    auto wins2 = std::uint64_t{0};
    for (auto const& [roll, multiplicity]: dice) {
        auto const position = (p1 + roll) % 10;
        auto const score = s1 + position + 1;
        if (score >= 21) {
            wins1 += multiplicity;
        }
        else {
            auto const [w2, w1] = part_2(p2, position, s2, score);
            wins1 += w1 * multiplicity;
            wins2 += w2 * multiplicity;
        }
    }
    return std::pair{wins1, wins2};
}

auto main() -> int {
    std::cout << part_1(std::array{
        Player{.name = 0, .position = 2, .score = 0},
        Player{.name = 1, .position = 9, .score = 0},
    }) << "\n";
    auto solution = part_2(2, 9, 0, 0);
    std::cout << std::max(solution.first, solution.second) << "\n";
}
