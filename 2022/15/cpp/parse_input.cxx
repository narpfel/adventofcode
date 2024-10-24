export module parse_input;

import ctre;
import std;

namespace rng = std::ranges;

using i64 = std::int64_t;

export using Coords = std::vector<std::tuple<std::tuple<i64, i64>, std::tuple<i64, i64>>>;

auto parse(std::string_view const s) -> i64 {
    auto value = i64{};
    auto const [_, ec] = std::from_chars(&s.front(), (&s.front()) + rng::size(s), value);
    if (ec == std::errc{}) {
        return value;
    }
    else {
        throw std::invalid_argument{std::format("could not parse: {}", s)};
    }
}

export auto read_input(auto const& filename) -> Coords {
    constexpr static auto sensor_re = ctre::match<
        R"(Sensor at x=(?<sensor_x>-?\d+), y=(?<sensor_y>-?\d+): )"
        R"(closest beacon is at x=(?<beacon_x>-?\d+), y=(?<beacon_y>-?\d+))"
    >;

    auto input = std::ifstream{filename};
    auto coords = Coords{};
    for (auto line = std::string{}; std::getline(input, line);) {
        auto const captures = sensor_re(line);
        coords.emplace_back(
            std::tuple{parse(captures.get<"sensor_x">()), parse(captures.get<"sensor_y">())},
            std::tuple{parse(captures.get<"beacon_x">()), parse(captures.get<"beacon_y">())}
        );
    }
    return coords;
}
