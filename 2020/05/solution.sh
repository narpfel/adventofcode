#!/usr/bin/env bash

read_input() {
    < "$1" sed -e 'y/FLBR/0011/;s/^/ibase=2;obase=A;/' | bc | sort -n
}

part1() {
    echo "$1" | tail -n1
}

part2() {
    minimum_seat_number=$(echo "$1" | head -n1)
    maximum_seat_number=$(echo "$1" | tail -n1)
    comm \
        -23 \
        <(seq $minimum_seat_number $maximum_seat_number) \
        <(echo "$1")
}

main() {
    input="$(read_input input)"
    part1 "$input"
    part2 "$input"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
    main "$@"
fi
