#!/usr/bin/env bash

n=50; < input tr LR -+ | while read line; do ((n = (n $line + 100) % 100)); echo $n; done | grep -c '^0$'

n=50
part_2=0
while read line; do
    ((step = line < 0 ? -1 : 1))
    ((step_count = line < 0 ? -line : line))
    for ((i = 0; i < step_count; ++i)); do
        ((n = (n + step + 100) % 100, n == 0 && ++part_2))
    done
done < <(tr LR -+ < input)
echo $part_2
