#define _GNU_SOURCE
#include <inttypes.h>
#include <iso646.h>
#include <stdbit.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define lengthof(xs) (sizeof(xs) / sizeof((xs)[0]))

// FIXME: clang 18 doesn’t support `constexpr`
enum: size_t { node_count = 26 * 26 };

typedef struct NodeSet {
    uint64_t bits[node_count / 64 + 1];
} NodeSet;

void set_add(NodeSet* const set, size_t const bit) {
    auto const i = bit / 64;
    auto const j = bit % 64;
    set->bits[i] |= 1ull << j;
}

void set_remove(NodeSet* const set, size_t const bit) {
    auto const i = bit / 64;
    auto const j = bit % 64;
    set->bits[i] &= ~(1ull << j);
}

size_t set_popcount(NodeSet const* const set) {
    size_t popcount = 0;
    for (size_t i = 0; i < lengthof(set->bits); ++i) {
        popcount += stdc_count_ones(set->bits[i]);
    }
    return popcount;
}

size_t set_tzcount(NodeSet const* const set) {
    for (size_t i = 0; i < lengthof(set->bits); ++i) {
        auto chunk = set->bits[i];
        if (chunk != 0) {
            return 64 * i + stdc_trailing_zeros(chunk);
        }
    }
    return node_count;
}

bool set_any(NodeSet const* const set) {
    for (size_t i = 0; i < lengthof(set->bits); ++i) {
        if (set->bits[i]) {
            return true;
        }
    }
    return false;
}

NodeSet set_intersection(NodeSet const* const lhs, NodeSet const* const rhs) {
    auto result = *lhs;
    for (size_t i = 0; i < lengthof(lhs->bits); ++i) {
        result.bits[i] &= rhs->bits[i];
    }
    return result;
}

void set_print(NodeSet const* const set) {
    puts("struct NodeSet {\n    uint64_t[11] bits = {");
    for (size_t i = 0; i < lengthof(set->bits); ++i) {
        printf("        [%2zu] = 0b%064" PRIb64 ",\n", i, set->bits[i]);
    }
    puts("    },\n}");
}

size_t parse_node(char const* const node) {
    return (size_t)((node[0] - 'a') * 26 + (node[1] - 'a'));
}

NodeSet* read_input(char const* const filename) {
    auto const file = fopen(filename, "r");
    if (not file) {
        return nullptr;
    }
    NodeSet* const connections = calloc(node_count + 2, sizeof *connections);
    char* line = nullptr;
    NodeSet starts_with_t = {};
    NodeSet all_connections = {};
    for (size_t n = 0; getline(&line, &n, file) > 1;) {
        auto const a = parse_node(line);
        auto const b = parse_node(line + 3);
        set_add(&connections[a], b);
        set_add(&connections[b], a);
        set_add(&all_connections, a);
        set_add(&all_connections, b);
        if (line[0] == 't') {
            set_add(&starts_with_t, a);
        }
        if (line[3] == 't') {
            set_add(&starts_with_t, b);
        }
    }
    fclose(file);
    free(line);
    connections[node_count] = starts_with_t;
    connections[node_count + 1] = all_connections;
    return connections;
}

void bron_kerbosch(
    NodeSet const* const connections,
    NodeSet const r,
    NodeSet p,
    size_t* const part_1_result,
    NodeSet* const part_2_result,
    size_t* const max_len
) {
    auto const length = set_popcount(&r);
    if (length == 3) {
        auto const intersection = set_intersection(&r, &connections[node_count]);
        if (set_any(&intersection)) {
            *part_1_result += 1;
        }
    }
    if (length > *max_len) {
        *max_len = length;
        *part_2_result = r;
    }

    while (set_any(&p)) {
        auto const i = set_tzcount(&p);
        auto new_r = r;
        set_add(&new_r, i);
        bron_kerbosch(
            connections,
            new_r,
            set_intersection(&p, &connections[i]),
            part_1_result,
            part_2_result,
            max_len
        );
        set_remove(&p, i);
    }
}

int main() {
    auto const connections = read_input("input");
    size_t part_1_result = 0;
    NodeSet part_2_result = {};
    size_t max_len = 0;
    auto const all_connections = connections[node_count + 1];
    bron_kerbosch(
        connections,
        (NodeSet){},
        all_connections,
        &part_1_result,
        &part_2_result,
        &max_len
    );
    printf("%zu\n", part_1_result);
    char result[node_count * 3 + 1] = {};
    size_t i = 0;
    while (set_any(&part_2_result)) {
        auto const node = set_tzcount(&part_2_result);
        result[i++] = ',';
        result[i++] = (char)((node / 26) + 'a');
        result[i++] = (char)((node % 26) + 'a');
        set_remove(&part_2_result, node);
    }
    puts(result + 1);
    free(connections);
}
