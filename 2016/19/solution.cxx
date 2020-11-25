#include <cstdint>

#include <iostream>
#include <list>
#include <ranges>

constexpr auto input = std::uint64_t{3'014'387};

auto circular_next(auto& container, auto it) {
    using std::begin, std::end;
    ++it;
    if (it == end(container)) {
        return begin(container);
    }
    else {
        return it;
    }
}

auto generate_elves(std::uint64_t const size) -> std::list<std::uint64_t> {
    auto elf_numbers = std::ranges::views::iota(std::uint64_t{1}, size + 1);
    auto elves = std::list<std::uint64_t>{};
    std::for_each(
        std::begin(elf_numbers),
        std::end(elf_numbers),
        [&](auto const i) { elves.push_back(i); }
    );
    return elves;
}

auto part1(std::list<std::uint64_t> elves) -> std::uint64_t {
    for (auto elf = begin(elves); size(elves) > 1; elf = circular_next(elves, elf)) {
        elves.erase(circular_next(elves, elf));
    }
    return elves.front();
}

auto part2(std::list<std::uint64_t> elves) -> std::uint64_t {
    auto opposite_elf = std::next(begin(elves), size(elves) / 2);
    auto elf = begin(elves);
    while (size(elves) > 1) {
        auto stolen_from = opposite_elf;
        opposite_elf = circular_next(elves, opposite_elf);
        if (size(elves) % 2 != 0) {
            opposite_elf = circular_next(elves, opposite_elf);
        }
        elves.erase(stolen_from);
        elf = circular_next(elves, elf);
    }
    return elves.front();
}

auto main() -> int {
    std::cout << part1(generate_elves(input)) << '\n';
    std::cout << part2(generate_elves(input)) << '\n';
}
