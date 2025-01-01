#define _GNU_SOURCE
#include <iso646.h>
#include <stdbit.h>
#include <stdio.h>
#include <stdlib.h>

constexpr size_t node_count = 26 * 26;

typedef unsigned _BitInt(node_count) NodeSet;

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
    NodeSet starts_with_t = 0;
    NodeSet all_connections = 0;
    for (size_t n = 0; getline(&line, &n, file) > 1;) {
        auto const a = parse_node(line);
        auto const b = parse_node(line + 3);
        auto const node_a = (NodeSet)1 << a;
        auto const node_b = (NodeSet)1 << b;
        connections[a] |= node_b;
        connections[b] |= node_a;
        all_connections |= node_a;
        all_connections |= node_b;
        if (line[0] == 't') {
            starts_with_t |= node_a;
        }
        if (line[3] == 't') {
            starts_with_t |= node_b;
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
    size_t const length = stdc_count_ones(r);
    if (length == 3 && r & connections[node_count]) {
        *part_1_result += 1;
    }
    if (length > *max_len) {
        *max_len = length;
        *part_2_result = r;
    }

    while (p) {
        size_t const i = stdc_trailing_zeros(p);
        auto const v = ((NodeSet)1) << i;
        bron_kerbosch(
            connections,
            r | v,
            p & connections[i],
            part_1_result,
            part_2_result,
            max_len
        );
        p -= v;
    }
}

int main() {
    auto const connections = read_input("input");
    size_t part_1_result = 0;
    NodeSet part_2_result = 0;
    size_t max_len = 0;
    auto const all_connections = connections[node_count + 1];
    bron_kerbosch(connections, 0, all_connections, &part_1_result, &part_2_result, &max_len);
    printf("%zu\n", part_1_result);
    char result[node_count * 3 + 1] = {};
    size_t i = 0;
    while (part_2_result) {
        auto const node = stdc_trailing_zeros(part_2_result);
        result[i++] = ',';
        result[i++] = (char)((node / 26) + 'a');
        result[i++] = (char)((node % 26) + 'a');
        part_2_result -= ((NodeSet)1) << node;
    }
    puts(result + 1);
    free(connections);
}
