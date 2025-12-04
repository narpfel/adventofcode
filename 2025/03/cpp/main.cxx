import std;

namespace rng = std::ranges;
namespace rv = std::ranges::views;

using u8 = std::uint8_t;
using u64 = std::uint64_t;
using usize = std::size_t;

template<usize N>
[[gnu::always_inline]] inline auto select_ith(
    std::string_view const bank,
    std::array<u8, N> indices,
    usize const i,
    usize const j
) -> std::tuple<
    std::array<char, N>,
    std::array<u8, N>
> {
    indices[j] = static_cast<u8>(i);
    rng::inplace_merge(rng::begin(indices), rng::begin(indices) + j, rng::begin(indices) + j + 1uz);
    auto selected = std::array<char, N>{};
    for (auto const i: rv::iota(0uz, j + 1uz)) {
        selected[i] = bank[indices[i]];
    }
    return std::tuple{selected, indices};
}

template<usize N>
auto select_best(std::string_view const bank) -> u64 {
    auto selected = std::array<char, N>{};
    auto indices = std::array<u8, N>{};
    for (auto const j: rv::iota(0uz, N)) {
        std::tie(selected, indices) = rng::max(
            rv::iota(0uz, rng::size(bank))
            | rv::filter([&](auto const i) { return not rng::contains(indices | rv::take(j), i); })
            | rv::transform([&](auto const i) { return select_ith<N>(bank, indices, i, j); })
        );
    }
    auto best = u64{};
    auto const result =
        std::from_chars(rng::data(selected), rng::data(selected) + rng::size(selected), best);
    if (result.ec != std::errc{}) {
        std::println("could not parse {}", selected);
        std::exit(1);
    }
    return best;
}

template<usize N>
auto solve(std::span<std::string const> const banks) -> u64 {
    return std::transform_reduce(
        rng::begin(banks),
        rng::end(banks),
        u64{0},
        std::plus{},
        [](auto const& bank) { return select_best<N>(bank); }
    );
}

auto main() -> int {
    auto input = std::ifstream{"input"};
    auto const banks = std::vector(
        std::istream_iterator<std::string>{input},
        std::istream_iterator<std::string>{}
    );
    std::println("{}", solve<2uz>(banks));
    std::println("{}", solve<12uz>(banks));
}
