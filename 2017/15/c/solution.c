#include <stdint.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>

typedef uint32_t u32;

#define MODULUS UINT32_C(2147483647)

u32 lehmer_rng(
    u32 const modulus,
    u32 const a,
    u32 const x
) {
    return ((uint64_t)a * x) % modulus;
}

u32 part1(u32 a, u32 b) {
    u32 result = 0;
    for (u32 i = 0; i < 40000000; ++i) {
        a = lehmer_rng(MODULUS, 16807, a);
        b = lehmer_rng(MODULUS, 48271, b);
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
}

u32 part2(u32 a, u32 b) {
    u32 result = 0;
    for (u32 i = 0; i < 5000000; ++i) {
        while (true) {
            a = lehmer_rng(MODULUS, 16807, a);
            if ((a % 4) == 0) {
                break;
            }
        }
        while (true) {
            b = lehmer_rng(MODULUS, 48271, b);
            if ((b % 8) == 0) {
                break;
            }
        }
        result += (a & 0xffff) == (b & 0xffff);
    }
    return result;
}

int main() {
    printf("%" PRIu32 "\n", part1(116, 299));
    printf("%" PRIu32 "\n", part2(116, 299));
}
