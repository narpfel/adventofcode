#!/usr/bin/env zsh
n(){sed 'y/FLBR/0011/;s/^/ibase=2;/'<i|sort|bc};n|tail -1;n|comm -23 <(seq `n|sed -n '1p;$p'`) -
