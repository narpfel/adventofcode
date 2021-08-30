#include <cstdint>

#include <array>
#include <charconv>
#include <fstream>
#include <iostream>
#include <iterator>
#include <optional>
#include <regex>
#include <tuple>
#include <vector>

#include <range/v3/all.hpp>

using Ingredient = std::array<int64_t, 4>;
using Ingredients = std::vector<Ingredient>;
using Combinations = std::vector<std::tuple<std::vector<int64_t>, uint64_t>>;

constexpr auto ingredient_pattern =
    R"(\w+: )"
    R"(capacity (-?\d+), )"
    R"(durability (-?\d+), )"
    R"(flavor (-?\d+), )"
    R"(texture (-?\d+), )"
    R"(calories (\d+))";

auto score(
    ranges::input_range auto const& amount_per_ingredient,
    ranges::input_range auto const& transposed_ingredients
) -> uint64_t {
    return ranges::accumulate(
        transposed_ingredients,
        uint64_t{1},
        std::multiplies{},
        [&](auto const& property) {
            return std::max(
                int64_t{0},
                ranges::inner_product(property, amount_per_ingredient, int64_t{0})
            );
        }
    );
}

auto cartesian_product(ranges::forward_range auto const range, size_t const repeat) {
    constexpr static auto dereference = [](auto it) { return *it; };
    auto iters = std::vector{repeat, ranges::begin(range)};
    auto const infinite_product = ranges::views::generate(
        [range, iters]() mutable
        -> std::optional<decltype(iters | ranges::views::transform(dereference))> {
            auto carry = true;
            for (auto& it: iters) {
                if (not carry) {
                    break;
                }
                ++it;
                carry = it == ranges::end(range);
                if (carry) {
                    it = ranges::begin(range);
                }
            }
            if (carry) {
                return std::nullopt;
            }
            else {
                return iters | ranges::views::transform(dereference);
            }
        }
    );
    return ranges::take_while_view(infinite_product, std::identity{})
        | ranges::views::transform(dereference);
}

auto possible_combinations(int64_t const n, Ingredients const& ingredients) -> Combinations {
    auto const transposed_ingredients = [&]() {
        auto result = ingredients;
        for (auto i = 0uz; i < size(result); ++i) {
            for (auto j = 0uz; j < i; ++j) {
                std::swap(result[i][j], result[j][i]);
            }
        }
        return result;
    }();

    using ranges::views::iota;
    constexpr auto zero = int64_t{0};
    return
        cartesian_product(iota(zero, n), ranges::size(ingredients))
        | ranges::views::filter([](auto const& amount_per_ingredient) {
            return ranges::accumulate(amount_per_ingredient, 0) == 100;
        })
        | ranges::views::transform([&](auto const& amount_per_ingredient) {
            auto const amount_per_ingredient2 = amount_per_ingredient | ranges::to_vector;
            return std::tuple{
                amount_per_ingredient2,
                score(amount_per_ingredient2, transposed_ingredients)
            };
        })
        | ranges::to_vector;
}

auto part1(Combinations const& combinations) -> int64_t {
    auto const xs = combinations
        | ranges::views::transform([](auto const& combination) { return std::get<1>(combination); });
    return *ranges::max_element(xs);
}

auto part2(
    Combinations const& combinations,
    std::vector<int64_t> const& calories_per_ingredient
) -> int64_t {
    auto xs = combinations
        | ranges::views::filter([&](auto const& combination) {
            return ranges::inner_product(std::get<0>(combination), calories_per_ingredient, 0)
                == 500;
        })
        | ranges::views::transform([](auto const& combination) { return std::get<1>(combination); });
    return *ranges::max_element(xs);
}

auto main() -> int {
    auto ingredients = Ingredients{};
    auto calories_per_ingredient = std::vector<int64_t>{};
    auto const ingredient_re = std::regex{ingredient_pattern};
    auto input_file = std::ifstream{"input"};
    for (auto line = std::string{}; std::getline(input_file, line);) {
        if (auto match = std::cmatch{}; std::regex_match(line.c_str(), match, ingredient_re)) {
            ingredients.emplace_back();
            auto number = int64_t{};
            for (auto i: ranges::views::iota(1, 5)) {
                if (
                    auto [ptr, error_code]
                        = std::from_chars(match[i].first, match[i].second, number);
                    error_code == std::errc{}
                ) {
                    ingredients.back()[i - 1] = number;
                }
                else {
                    return 1;
                }
            }
            if (
                auto [ptr, error_code] = std::from_chars(match[5].first, match[5].second, number);
                error_code == std::errc{}
            ) {
                calories_per_ingredient.emplace_back(number);
            }
            else {
                return 2;
            }
        }
        else {
            return 3;
        }
    }

    auto const combinations = possible_combinations(100, ingredients);
    std::cout << part1(combinations) << '\n';
    std::cout << part2(combinations, calories_per_ingredient) << '\n';
}
