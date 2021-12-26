#include <cstdint>

#include <iostream>

constexpr auto modulus = std::uint64_t{2147483647};

auto lehmer_rng(
    std::uint64_t const modulus,
    std::uint64_t const a,
    std::uint64_t const x
) -> std::uint64_t {
    return (a * x) % modulus;
}

auto part1(std::uint64_t a, std::uint64_t b) -> std::size_t {
    auto result = 0uz;
    for (auto i = 0uz; i < 40'000'000uz; ++i) {
        a = lehmer_rng(modulus, 16807, a);
        b = lehmer_rng(modulus, 48271, b);
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
}

auto part2(std::uint64_t a, std::uint64_t b) -> std::size_t {
    auto result = 0uz;
    for (auto i = 0uz; i < 5'000'000; ++i) {
        while (true) {
            a = lehmer_rng(modulus, 16807, a);
            if ((a % 4) == 0) {
                break;
            }
        }
        while (true) {
            b = lehmer_rng(modulus, 48271, b);
            if ((b % 8) == 0) {
                break;
            }
        }
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
}

auto main() -> int {
    std::cout << part1(116, 299) << '\n';
    std::cout << part2(116, 299) << '\n';
}
