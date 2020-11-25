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

auto main() -> int {
    auto elf_numbers = std::ranges::views::iota(std::uint64_t{1}, input + 1);
    auto elves = std::list<std::uint64_t>{};
    std::for_each(
        std::begin(elf_numbers),
        std::end(elf_numbers),
        [&](auto const i) { elves.push_back(i); }
    );
    for (auto it = begin(elves); size(elves) > 1; it = circular_next(elves, it)) {
        elves.erase(circular_next(elves, it));
    }
    std::cout << elves.front() << '\n';
}
