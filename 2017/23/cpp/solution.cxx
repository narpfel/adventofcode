#include <cstdint>

#include <iostream>


auto is_product_of_two_integers(uint64_t const n) -> bool {
    for (auto i = uint64_t{2}; i < n / 2; ++i) {
        if (n % i == 0) {
            return true;
        }
    }
    return false;
}


auto run(int64_t const a) -> int64_t {
    int64_t b = 0, c = 0, d = 0, e = 0, f = 0, h = 0;
    auto muls_executed = int64_t{0};

    b = 81;
    c = b;
    if (a != 0) {
        b *= 100;
        ++muls_executed;
        b += 100'000;
        c = b + 17'000;

        // Rewriting the assembly in slightly more readable C++ makes the
        // algorithm more or less obvious: It counts the number of composite
        // numbers between `b` and `c` (inclusive).
        for (auto i = uint64_t{0}; i <= 1000; ++i) {
            auto num = b + 17 * i;
            if (is_product_of_two_integers(num)) {
                ++h;
            }
        }
        return h;
    }

    while (true) {
        f = 1;
        d = 2;
        do {
            e = 2;
            do {
                ++muls_executed;
                if (d * e == b) {
                    f = 0;
                }
                ++e;
            }
            while (e != b);
            ++d;
        } while (d != b);
        if (f == 0) {
            ++h;
        }
        if (b == c) {
            return muls_executed;
        }
        b += 17;
    }
}

auto main() -> int {
    std::cout << run(0) << '\n';
    std::cout << run(1) << '\n';
}
