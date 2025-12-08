from itertools import*;*a,o=open(0);s=str.split;b=map("".join,zip(*a));o=[o.join for o in s(o)]
print(sum(eval(o(a))for o,*a in zip(o,*map(s,a))),sum(eval(o(takewhile(str.strip,b)))for o in o))
