#include <cassert>
#include <cstdint>

#include <fstream>
#include <functional>
#include <iostream>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

#include <range/v3/all.hpp>

using u8 = std::uint8_t;
using u64 = std::uint64_t;
using usize = std::size_t;

struct Literal {
    u64 literal;
};
struct Sum {};
struct Product {};
struct Minimum {};
struct Maximum {};
struct GreaterThan {};
struct LessThan {};
struct Equals {};

using Type = std::variant<Literal, Sum, Product, Minimum, Maximum, GreaterThan, LessThan, Equals>;

auto type_for_id(u64 const type_id) -> Type {
    switch (type_id) {
        case 0: return Sum{};
        case 1: return Product{};
        case 2: return Minimum{};
        case 3: return Maximum{};
        case 4: assert(false and "unreachable");
        case 5: return GreaterThan{};
        case 6: return LessThan{};
        case 7: return Equals{};
        default: assert(false and "unreachable");
    }
}

template<typename... F>
struct overload: F... {
    using F::operator()...;
};

struct Packet {
    u64 version;
    Type type;
    std::vector<Packet> children;

    auto version_sum() const -> u64 {
        return this->version
            + ranges::accumulate(this->children, u64{0}, std::plus{}, &Packet::version_sum);
    }

    auto evaluate() const -> u64 {
        return std::visit(overload{
                [](Literal literal) -> u64 { return literal.literal; },
                [this](Sum) -> u64 {
                    return ranges::accumulate(children, u64{0}, std::plus{}, &Packet::evaluate);
                },
                [this](Product) -> u64 {
                    return ranges::accumulate(children, u64{1}, std::multiplies{}, &Packet::evaluate);
                },
                [this](Minimum) -> u64 {
                    constexpr auto max = std::numeric_limits<u64>::max();
                    return ranges::accumulate(children, max, ranges::min, &Packet::evaluate);
                },
                [this](Maximum) -> u64 {
                    constexpr auto min = std::numeric_limits<u64>::min();
                    return ranges::accumulate(children, min, ranges::max, &Packet::evaluate);
                },
                [this](GreaterThan) -> u64 {
                    return ranges::is_sorted(children, std::greater_equal{}, &Packet::evaluate);
                },
                [this](LessThan) -> u64 {
                    return ranges::is_sorted(children, std::less_equal{}, &Packet::evaluate);
                },
                [this](Equals) -> u64 {
                    return ranges::is_sorted(children, std::not_equal_to{}, &Packet::evaluate);
                }
            },
            this->type
        );
    }
};

struct Parser {
    std::vector<u8> bits;
    size_t cursor = 0;

    Parser(std::string_view const transmission) {
        for (auto c: transmission | ranges::views::reverse) {
            auto nibble = c <= '9' ? c - '0' : c - 'A' + 10;
            for ([[maybe_unused]] auto _: ranges::views::iota(0uz, 4uz)) {
                bits.emplace_back(nibble & 1);
                nibble >>= 1;
            }
        }
        ranges::reverse(bits);
    }

    auto next(usize const n) -> u64 {
        auto result = u64{0};
        for (auto const end = cursor + n; cursor < end; ++cursor) {
            result <<= 1;
            result |= bits[cursor];
        }
        return result;
    }

    auto parse() -> Packet {
        auto const version = next(3);
        auto const type_id = next(3);
        if (type_id == 4) {
            auto literal = u64{0};
            while (true) {
                auto const is_last_group = next(1) == 0;
                literal <<= 4;
                literal |= next(4);
                if (is_last_group) {
                    return Packet{version, Literal{literal}, {}};
                }
            }
        }
        else {
            auto const length_type = next(1);
            auto children = std::vector<Packet>{};
            if (length_type == 0) {
                auto const length = next(15);
                auto const end = cursor + length;
                while (cursor < end) {
                    children.emplace_back(parse());
                }
            }
            else {
                auto const child_count = next(11);
                for ([[maybe_unused]] auto _: ranges::views::iota(u64{0}, child_count)) {
                    children.emplace_back(parse());
                }
            }
            return Packet{version, type_for_id(type_id), std::move(children)};
        }
    }
};

auto parse_packet(std::string_view const transmission) -> Packet {
    auto parser = Parser{transmission};
    return parser.parse();
}

auto main() -> int {
    auto file = std::ifstream{"input"};
    if (not file.good()) {
        return 1;
    }
    auto transmission = std::string{};
    std::getline(file, transmission);
    auto const packet = parse_packet(transmission);
    std::cout << packet.version_sum() << "\n";
    std::cout << packet.evaluate() << "\n";
}
