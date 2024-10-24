import std;
import parse_input;

namespace rng = std::ranges;
namespace rv = std::ranges::views;

using i64 = std::int64_t;

auto enumerate() {
    return rv::transform([i = 0uz](auto&& value) mutable {
        return std::make_tuple(i++, std::forward<decltype(value)>(value));
    });
}

template<typename T>
auto vec_with_capacity(std::size_t const capacity) -> std::vector<T> {
    auto vec = std::vector<T>{};
    vec.reserve(capacity);
    return vec;
}

template<typename T>
struct Sparse {
    std::vector<T> values = vec_with_capacity<T>(32uz);
    std::vector<T> scratch = vec_with_capacity<T>(32uz);

    auto clear(this Sparse& self) -> void {
        self.values.clear();
        self.scratch.clear();
    }

    auto insert(this Sparse& self, T lo, T hi) -> void {
        rng::swap(self.values, self.scratch);
        self.values.clear();
        auto i = 0uz;
        auto j = 0uz;
        for (auto const& [n, x]: self.scratch | enumerate()) {
            if (x < lo) {
                i = n + 1;
            }
            if (x <= hi) {
                j = n + 1;
            }
            else {
                break;
            }
        }
        self.values.append_range(self.scratch | rv::take(i));
        if (i % 2 == 0 and j % 2 == 0) {
            self.values.emplace_back(std::move(lo));
            self.values.emplace_back(std::move(hi));
        }
        else if (i % 2 == 0 and j % 2 != 0) {
            self.values.emplace_back(std::move(lo));
        }
        else if (i % 2 != 0 and j % 2 == 0) {
            self.values.emplace_back(std::move(hi));
        }
        self.values.append_range(self.scratch | rv::drop(j));
    }

    auto compactify(this Sparse& self) -> void {
        if (self.values.empty()) {
            return;
        }
        auto values = std::move(self.values);
        auto last = values.back();
        values.pop_back();
        self.values.emplace_back(std::move(values.front()));
        auto i = 1uz;
        for (; i < rng::size(values); i += 2) {
            auto&& x = std::move(values.at(i));
            auto&& y = std::move(values.at(i + 1));
            if (y != x + 1) {
                self.values.emplace_back(std::move(x));
                self.values.emplace_back(std::move(y));
            }
        }
        if (i != rng::size(values)) {
            throw std::logic_error{"invalid Sparse set state: length is not a multiple of 2"};
        }
        self.values.emplace_back(std::move(last));
    }

    auto length(this Sparse const& self) -> i64 {
        auto result = i64{0};
        for (auto i = 0uz; i < rng::size(self.values); i += 2) {
            auto const& lo = self.values.at(i);
            auto const& hi = self.values.at(i + 1);
            result += hi - (lo - 1);
        }
        return result;
    }

    auto contains(this Sparse const& self, T const& value) -> bool {
        for (auto i = 0uz; i < rng::size(self.values); i += 2) {
            auto const& lo = self.values.at(i);
            auto const& hi = self.values.at(i + 1);
            if (lo <= value and value <= hi) {
                return true;
            }
        }
        return false;
    }
};

template<typename T>
auto blocked_in_line(Coords const& coords, i64 const target_y, Sparse<T>& blocked) -> void {
    blocked.clear();
    for (auto const& line: coords) {
        auto const& [sensor, beacon] = line;
        auto const& [sx, sy] = sensor;
        auto const& [bx, by] = beacon;
        auto const sensor_range = std::abs(sx - bx) + std::abs(sy - by);
        auto const distance = std::abs(target_y - sy);
        if (distance <= sensor_range) {
            auto const line_length = (sensor_range - distance) * 2 + 1;
            blocked.insert(sx - line_length / 2, sx + line_length / 2);
        }
    }
}

auto part_1(Coords const& coords, i64 const target_y) -> i64 {
    auto const blocked = [&] {
        auto blocked = Sparse<i64>{};
        blocked_in_line(coords, target_y, blocked);
        blocked.compactify();
        return blocked;
    }();
    auto const blocked_position_count = blocked.length();
    return blocked_position_count - rng::ssize(
        coords
        | rv::filter([&](auto const& line) {
            auto const& [x, y] = std::get<1>(line);
            return y == target_y and blocked.contains(x);
        })
        | rv::transform([](auto const& line) -> i64 {
            auto const& [x, _] = std::get<1>(line);
            return x;
        })
        | rng::to<std::unordered_set>()
    );
}

auto part_2(Coords const& coords, i64 const max_y) -> i64 {
    auto blocked = Sparse<i64>{};
    for (auto const y: rv::iota(i64{0}, max_y)) {
        blocked_in_line(coords, y, blocked);
        if ((rng::size(blocked.values) / 2) % 2 == 0) {
            blocked.compactify();
            auto const x = blocked.values.at(1) + 1;
            return x * 4'000'000 + y;
        }
    }
    throw std::logic_error{"unreachable"};
}

auto main() -> int {
    auto const input = read_input("input");
    std::println("{}", part_1(input, 2'000'000));
    std::println("{}", part_2(input, 4'000'000));
}
