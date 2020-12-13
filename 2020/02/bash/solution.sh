#!/usr/bin/env bash

part1() {
    tr -d ':' < "$1" | while read input; do
        (
            line=($input)
            character=${line[1]}
            password=${line[2]}
            count=$(tr -cd $character <<< $password | wc -c)
            range=($(tr - ' ' <<< ${line[0]}))
            echo $(($count >= ${range[0]} && $count <= ${range[1]}))
        ) &
    done | grep -c 1
}

part2() {
    tr -d ':' < "$1" | while read input; do
        (
            line=($input)
            character=${line[1]}
            password=${line[2]}
            range=($(tr - ' ' <<< ${line[0]}))
            i=$((${range[0]} - 1))
            j=$((${range[1]} - 1))
            x=$(test ${password:$i:1} = $character && echo 1 || echo 0)
            y=$(test ${password:$j:1} = $character && echo 1 || echo 0)
            test $x -ne $y && echo 1 || echo 0
        ) &
    done | grep -c 1
}

main() {
    part1 input
    part2 input
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main
fi
