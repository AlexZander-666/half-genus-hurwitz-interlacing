"""Check the half-genus binomial formula from the recurrence and from original matching words."""
from fractions import Fraction as Q
from collections import Counter
from math import comb
from functools import cache
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from reduced_parameter import reduced
from pair_partitions import initial_matching, labeled_transitions

def binomial_row(m):
    return [Q(comb(2*m,2*j)-comb(m,j)**2,2) for j in range(m+1)]

def recursion_row(m):
    c=reduced(1,(m,));assert all(i==0 for i,j in c)
    return [m*sum(a*comb(j,k)*(-1)**(j-k) for (i,j),a in c.items() if j>=k)
            for k in range(m+1)]

def matching_row(m):
    # All connectedness tests here are automatic: the two pairings already connect all 2m labels.
    # Execute transpositions in decreasing order of their odd larger end.
    trans=cache(lambda m:tuple(labeled_transitions(m)))
    @cache
    def count(state,left,used):
        if left==0:
            return Counter({(0,0):1}) if all(v==(i^1) for i,v in enumerate(state)) else Counter()
        if len(state)<=2:return Counter()
        p=Counter()
        if state[-1]==len(state)-2:p.update(count(state[:-2],left,False))
        for _,next_state,flip in trans(state):
            for (h,f),val in count(next_state,left-1,True).items():
                p[h+int(not used),f+flip]+=val
        return p
    c=count(initial_matching((m,)),m,False)
    assert all(f==1 for h,f in c)
    return [c[j,1] for j in range(m+1)]

if __name__=='__main__':
    for m in range(1,31):
        p=binomial_row(m)
        assert p==recursion_row(m) and p==p[::-1]
        if m>=2:assert p[1]==p[-2]==m*(m-1)//2 and all(a>0 for a in p[1:-1])
        if m<=6:assert p==matching_row(m)
    print('PASS: all coefficient rows 1 through 30 from Corollary 4.16; original matching words on one-part degrees 1 through 6.')
