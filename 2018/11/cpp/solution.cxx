#include <cstdint>

#include <array>
#include <algorithm>
#include <iostream>
#include <iterator>
#include <numeric>
#include <optional>
#include <vector>


constexpr auto GRID_SIZE = size_t{300};
constexpr auto INPUT = int64_t{7672};

using Grid = std::vector<std::vector<int64_t>>;

struct Window {
    size_t x;
    size_t y;
    size_t window_size;
    int64_t total_power;
};


auto power_level(size_t const x, size_t const y, int64_t const serial_number) -> int64_t {
    auto const rack_id = static_cast<int64_t>(x) + 10;
    return ((((rack_id * static_cast<int64_t>(y) + serial_number) * rack_id) / 100) % 10) - 5;
}

auto calculate_grid(int64_t serial_number) -> Grid {
    auto grid = Grid{GRID_SIZE + 1, std::vector<int64_t>(GRID_SIZE + 1, 0)};
    for (auto y = size_t{0}; y < grid.size(); ++y) {
        for (auto x = size_t{0}; x < grid[y].size(); ++x) {
            grid[y][x] = power_level(x, y, serial_number);
        }
    }
    return grid;
}

auto precompute_sums(Grid& grid) -> void {
    for (auto& line: grid) {
        for (auto x = size_t{1}; x < line.size(); ++x) {
            line[x] += line[x - 1];
        }
    }
    for (auto y = size_t{1}; y < grid.size(); ++y) {
        for (auto x = size_t{0}; x < grid[y].size(); ++x) {
            grid[y][x] += grid[y - 1][x];
        }
    }
}

template<typename OutputIt>
auto windowed(Grid const& grid, size_t window_size, OutputIt out) -> void {
    auto const y = grid.size();
    auto const x = grid.at(0).size();
    for (auto i = size_t{1}; i < x - window_size; ++i) {
        for (auto j = size_t{1}; j < y - window_size; ++j) {
            auto const a = grid[j][i];
            auto const b = grid[j][i + window_size];
            auto const c = grid[j + window_size][i + window_size];
            auto const d = grid[j + window_size][i];
            auto const power_level = c + a - d - b;
            *out++ = Window{i + 1, j + 1, window_size, int64_t{power_level}};
        }
    }
}

template<typename T, auto compare = std::less<T>{}>
struct Maximum {
    using value_type = T;

    std::optional<T> maximum;

    auto push_back(T&& t) -> void {
        if (not maximum or compare(*maximum, t)) {
            maximum.emplace(std::forward<T>(t));
        }
    }
};

template<typename It>
auto solve(Grid const& grid, It const first, It const last) -> Window {
    auto solution = Maximum<
        Window,
        [](auto const& lhs, auto const& rhs) { return lhs.total_power <= rhs.total_power; }
    >{};
    auto inserter = std::back_inserter(solution);
    std::for_each(first, last, [&](auto const& window_size) {
        windowed(grid, window_size, inserter);
    });
    return *solution.maximum;
}

auto main() -> int {
    auto const power_levels = []() {
        auto ps = calculate_grid(INPUT);
        precompute_sums(ps);
        return ps;
    }();
    auto const grid_sizes = []() {
        auto grid_sizes = std::array<size_t, GRID_SIZE + 1>{};
        std::iota(begin(grid_sizes), end(grid_sizes), 0);
        return grid_sizes;
    }();
    auto const part1 = solve(power_levels, begin(grid_sizes) + 3, begin(grid_sizes) + 4);
    std::cout << part1.x << ',' << part1.y << '\n';
    auto const part2 = solve(power_levels, begin(grid_sizes), end(grid_sizes));
    std::cout << part2.x << ',' << part2.y << ',' << part2.window_size << '\n';
}
