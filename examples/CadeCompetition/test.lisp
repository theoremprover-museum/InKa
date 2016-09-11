axiom all x,y:nat plus(x, s(y)) = s(plus(x, y));

all x:nat all y:nat difference(plus(x,y),x) = y;

all x:nat all y:nat difference(plus(y,x),x) = y;


dmac112 (all x:nat (all y:nat (all z:nat difference(plus(x,y),plus(x,z)) = difference(y,z))))

dmac287 (all x:nat times(x, 0) = 0)

dmac573 (all p:nat (all x:nat even(difference(p,x)) EQV (lessp(p,x) OR (even(p) EQV even(x)))))

dmac681 (all d:nat (all x:nat not lessp(x,difference(rt(x),d))))

dmac873 (all x:nat (all y:nat (all z:nat lessp(plus(x,y),plus(x,z)) EQV lessp(y,z))))

dmac1124 (all i:nat (all j:nat plus(difference(i,j),j) = if(leq(i,j),j,i)))

dmac1157 (all x:t619 (all y:t620 (all z:t621 not "zlesseqp*"(x,y) IMPL not lessp(m1(x,y,z),m1(zsub1(x),y,z)))))

dmac1166 all x:sexplist all y:sexplist all z:sexplist (not "zlesseqp*"(x,y) and m1(zsub1(y),z,x) = m1(x,y,z)) IMPL lessp(m3(zsub1(y),z,x),m3(x,y,z))
 
dmac1168 all x:natlist ordinalp("make-ordinal3"(x))



dmac686 (all i:nat (all j:nat not lessp(max2(i,j),"pr-apply"(i,j))))

dmac688 (all fn:nat,(all j:nat not lessp("max1*"(plus(j,fn),plus(j,fn)),"pr-apply"(fn,plus(j,fn)))))

dmac700 (all r0:t280 (all r1:nat (all r2:t281 (all r3:nat (all r4:nat "exp-fn"(r0,r1,r2,r3,r4) = times("exp***"(r3,r4),r1))))))
 
dmac816 (all i:nat (all j:nat (all k:nat "exp****"(i,plus(j,k)) = times("exp****"(i,j),"exp****"(i,k)))))


dmac155 (all y:nat remainder(0, y) = 0)

dmac584 (all a:nat (all n:nat (all p:nat remainder(times(times(a,s(n)),times(exp(a,n),fact(n))),p) = remainder(times(exp(a,s(n)),fact(s(n))),p))))

dmac591 (all a:nat,(all n:nat (all p:nat remainder("times-list"(reflections(n,a,s(p))),s(p)) = if("res1*"(n,a,s(p)),remainder(times(exp(a,n),fact(n)),s(p)),remainder(difference(s(p),remainder(times(exp(a,n),fact(n)),s(p))),s(p))))))


dmac596 (all a:nat (all i:nat (all j:nat (all p:nat (prime(p) and lessp(j,i) and lessp(i,p) and not divides(p,a)) IMPL not remainder(times(a,i),p) = remainder(times(a,j),p)))))

dmac617 (all a:nat (all p:nat (prime(p) and not p = 2 and not divides(p,a)) impl perm(positives(quotient(p,2)),reflections(quotient(p,2),a,p))))
 
dmac928 (all a:nat (all b:nat (all k:nat (all x:nat (not "divides*"(x,a) and a = "gcd*"(times(x,a),times(b,a))) impl not times(k,x) = times(b,a)))))

dmac929 (all b:nat (all x:nat (not "divides*"(x,b) and not x = 0 and not sub(x) = 0 and "prime1*"(x,sub(x))) impl "gcd*"(b,x) = 1))
 

dmac20  all x:list all y:list subbagp(bagint(x,y),x)

dmac59 (all i:nat even1(i) impl double(half(i)) = i)


dmac176 (all a:natall(b,pnat,all(k,pnat,(all x:nat (not divides(x,a) and a = gcd(times(x,a),times(b,a))) impl not times(k,x) = times(b,a))))))
 
dmac181 (all x:nat (all y:nat (prime(x) and not y = 1 and not x = y) impl not remainder(x,y) = 0))

dmac355 (all m:nat,(all n:nat (all p:nat (prime(p) and not remainder(m,p) = 0 and lessp(n,p)) impl "all-non-zerop"("s*"(n,m,p)))))

dmac361 (all k:nat (all m:nat (all p,{:(x,or(nat, not x = 0))}, (all q:nat
                       prime(q) impl remainder(times(m,exp(m,times(k,times(sub(p),sub(q))))),q) = remainder(m,q)))))

dmac362 (all ed:nat (all m:nat (all p:nat (all q:nat (prime(p) and prime(q) and not p = q and lessp(m,times(p,q)) and remainder(ed,times(sub(p),sub(q))) = 1) impl remainder(exp(m,ed),times(p,q)) = m))))

dmac422 (all a:nat (all j:nat (all p:nat (prime(p) and not divides(p,j) and not divides(p,a)) impl complement(complement(j,a,p),a,p) = remainder(j,p))))
 
dmac431 (all a:nat (all p:nat (prime(p) and not divides(p,a) and not residue(a,p)) impl "times-list"("comp-list"(sub(p),a,p)) = fact(sub(p)),pnat))

dmac475 (all a:nat (all i:nat (all j:nat (all p:nat (prime(p) and not divides({"int-2"},p) and not divides(p,a) and leq(i,quotient(p,{"int-2"})) and lessp(j,i)) impl not member(remainder(times(a,i),p),"reflect-list"(j,a,p))))))

dmac481 (all a:nat (all p:nat (prime(p) and not divides(2,p) and not divides(p,a),res1(quotient(p,2),a,p)) impl remainder(exp(a,quotient(p,2)),p) = 1))

dmac522 (all i:nat (all j:nat (all p:nat all(q,pnat, (prime(p) and prime(q) and not p = q and lessp(i,q) and lessp(j,p)) impl not member(times(i,p),mults(j,q))))))

dmac533 (all a:nat(all i:nat (all p:nat (prime(p) and not divides(p,a) and remainder(a,p) = remainder(times(i,i),p)) impl not divides(p,i))))


dmac213 (all i:nat all k:nat (i = 0 and leq(i,k)) IMPL sigma(i,k) = sigma(0, k))))

dmac339 (all n:nat listp(positives(n)) EQV not n = 0)

dmac243 all l:list all x:elem length(delete(x,l)) = if(member(x,l),length(list_cdr(l),length(l)))

dmac252 all n:nat "nbr-plus-fib"(n) = sub(fib(s(n)))

dmac319 all lst:natlist all r:nat "foldr-fn"(lst,r) = "foldl-fn"("reverse*"(lst),r)

dmac801 all a:list  all b:list "subsetp**"(a,b) impl union(a,b) = b

dmac661 all x:sexprlist listp(list_cdr(list_cdr(x))) IMPL "count*"(x) = s(s(plus("count*"(list_car({sexp},x)),plus("count*"(list_car({sexp},list_cdr({sexp},x))),"count*"(list_cdr({sexp},list_cdr({sexp},x)))))))


dmac834 all x:list "reverse-loop*"(x,nil) = "reverse**"(x)

dmac955 all v:nat all z:natlist not lessp(v,"maximum*"(z)) impl "addtolist2*"(v,"sort2*"(z)) = cons(v,"sort2*"(z)))

dmac982 all ac:nat all l:list "h-ac*"(l,ac) = "h-pr*"(l,ac)

dmac1016 (all board:list (all x:nat "length****"(board) = 9 impl iff(legalp(x,board),legalp1(x,board))))

dmac1037 (all opening:natlist (all xmoves1:natlist (all xmoves2:natlist "init-game"("length****"(opening),"tic-tac-toe"(append(opening,xmoves1))) = "init-game"("length****"(opening),"tic-tac-toe"(append(opening,xmoves2)))

dmac1084 all len:nat all n:nat "length****"("number->board"(n,len)) = len

