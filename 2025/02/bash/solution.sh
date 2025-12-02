#!/usr/bin/env bash
echo $(($(< input tr ,- '\n ' | while read lo hi; do seq $lo $hi | grep -E '^(.+)\1$' & done | paste -sd+)))
echo $(($(< input tr ,- '\n ' | while read lo hi; do seq $lo $hi | grep -E '^(.+)\1+$' & done | paste -sd+)))
