from collections import*;a,*l=open(0);n=Counter([a.find("S")]);s=0
for l in l:
 n=n-(p:=n)
 for x in p:
  q=p[x]
  if l[x]=="^":n[x-1]+=q;n[x+1]+=q;s+=1
  else:n[x]+=q
print(s,n.total())
