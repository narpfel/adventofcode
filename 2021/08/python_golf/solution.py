E={1:2,4:4,7:3,8:7}
f=frozenset;D=[(map(f,(a:=l.split())[:10]),map(f,a[11:]))for l in open("i")]
q=0
Q=0
for P,d in D:
 l={k:[]for k in range(9)}
 for p in P:l[len(p)]+=[p]
 m={d:l[E[d]][0]for d in E}
 for p in l[6]:m[p>=m[4]|m[7]and 9or not p>=m[1]and 6or 0]=p
 for p in l[5]:m[p>=m[1]and 3or p<m[6]and 5or 2]=p
 m={m[k]:k for k in m};n="".join(str(m[i])for i in d);q+=sum(int(i)in E for i in n);Q+=int(n)
print(q,Q)
