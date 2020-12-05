#!/usr/bin/env zsh
n=`sed 'y/FLBR/0011/;s/^/ibase=2;/'<i|sort|bc`;tail -n1<<<$n;comm -23 <(seq `sed -n '1p;$p'<<<$n`) <(<<<$n)
