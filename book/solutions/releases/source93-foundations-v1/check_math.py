"""Recompute worked values for all eighty Block 0 exercises.

Finite examples are not proofs of universal real statements. Those statements
have explicitly authored arguments, reviewed separately. Cosine enclosures here
use exact rational alternating-series bounds and outward rounding.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product
from math import factorial, floor, log, sin, cos, sqrt, ceil
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT/'book/solutions'))
import solution_review as h
from foundation_content import EXERCISES

BASE='book/solutions/releases/source93-foundations-v1'
checks=[]
document=h.Document(h.path(BASE+'/candidates/SafeLearning/primer-basics.html').read_bytes())
sources={h.clean(n.child('summary').text()):h.parts(document,n) for n in document.exercises()}


def check(code, description, computed, expected=True):
    assert computed == expected, (code,description,computed,expected)
    label=next(label for label in sources if label.split(' — ')[0] == 'Exercise '+code)
    checks.append(dict(exercise=code,label=label,check=description,passed=True,
                       solution_sha256=sources[label]['solution']['sha256']))


def orbit(mapping,start):
    seen=[]
    while start not in seen:
        seen.append(start);start=mapping[start]
    return seen


def trig_bounds(x,kind):
    assert F(0)<=x<=F(1)
    shift=0 if kind=='cos' else 1
    # Eighteen terms end with a negative term (a lower bound). The
    # nineteenth positive term supplies the next upper bound. Terms decrease
    # for 0 <= x <= 1, so the alternating-series remainder rule applies.
    low=sum(((-1)**j*x**(2*j+shift)/factorial(2*j+shift) for j in range(18)),F(0))
    high=low+x**(36+shift)/factorial(36+shift)
    return low,high


def round_out(low,high):
    scale=10**20
    return F(floor(low*scale),scale), F(ceil(high*scale),scale)


def main():
    # Six arithmetic warm-ups.
    check('0.W1','Power precedence and the two scalar distances',
          [(-3)**2,-3**2,(-2)**3,abs(-2-3),abs(2-(-3))],[9,-9,-8,5,5])
    check('0.W2','Common denominators, reciprocal and equation substitution',
          [F(1,4)+F(2,3),(F(1,2)+3)/4,2/F(1,2),F(1,3)+F(1,2)],
          [F(11,12),F(7,8),F(4),F(5,6)])
    check('0.W3','Four-term and three-term discounted sums',
          [F(2)**-3,F(1,2)**0,sum((F(1,2)**t for t in range(4)),F(0)),sum((F(1,2)**t for t in range(1,4)),F(0))],
          [F(1,8),F(1),F(15,8),F(7,8)])
    check('0.W4','Inequality endpoints and excluded neighbours',
          [-3*(-2)+2<=8,-3*0+2<=8,-3*(-3)+2<=8,1<=2*(-1)+3<7,1<=3<7,1<=2*2+3<7],
          [True,True,False,True,True,False])
    check('0.W5','Absolute-value and square interval boundaries',
          all((abs(x-2)<=3)==(-1<=x<=5) and (x*x<=4)==(-2<=x<=2) and (x*x<4)==(-2<x<2) for x in [F(i,4) for i in range(-20,25)]))
    check('0.W6','Exact power cutoff agrees with logarithm ceiling',
          F(3,16)>F(1,10)>F(3,32) and ceil(log(30)/log(2))==5)
    A={1,2};B={frozenset({1}),2}
    check('0.GS1','Membership, subset, empty subset and cardinalities',
          [1 in A,{1}<=A,frozenset({1}) in A,frozenset({1}) in B,set()<=A,len(A),len(B)],
          [True,True,False,True,True,2,2])
    S={('a','L'),('b','L'),('b','R')};X=['a','b'];U=['L','R']
    check('0.GS2','Enumerate all pairs and both quantified choices',
          len(list(product(X,U)))==4 and all(any((x,u) in S for u in U) for x in X) and {u for u in U if all((x,u) in S for x in X)}=={'L'})
    check('0.GS3','Four-row implication truth table',
          [not p or q for p,q in [(True,True),(True,False),(False,True),(False,False)]],[True,False,True,True])
    check('0.GS4','Feedback feasibility and endpoint disturbances',
          all(-1<=-x<=1 and all(abs(x-x+w)<=F(1,4) for w in [F(-1,4),F(0),F(1,4)]) for x in [F(i,4) for i in range(-4,5)]))
    f=lambda x:(2*x+1)/(x-1)
    check('0.GF1','Rational function evaluations and solved preimage',
          [f(F(0)),f(F(2)),f(F(4))],[F(-1),F(5),F(3)])
    check('0.GF2','Affine image/preimage endpoints and inverse compositions',
          [2*F(0)-1,2*F(2)-1,(F(0)+1)/2,(F(2)+1)/2],[-1,3,F(1,2),F(3,2)])
    check('0.GF3','Barrier values and the non-strict/strict sets',
          [4-(-2)**2,4-0**2,4-3**2],[0,4,-5])
    intervals=[]
    for x in [0,1,2,3,4]:
        lo,hi=max(-1,-x),min(1,2-x);intervals.append((lo,hi) if lo<=hi else None)
    check('0.GF4','Admissible command intervals and singleton endpoint',intervals,[(0,1),(-1,1),(-1,0),(-1,-1),None])
    check('0.GP1','Equivalence at and around its endpoint',all((x>=2)==(3*x+1>=7) for x in [F(i,2) for i in range(-10,11)]))
    check('0.GP2','Integer witnesses in the even and odd sum identities',all(2*m+2*n==2*(m+n) and (2*m+1)+(2*n+1)==2*(m+n+1) for m,n in product(range(-10,11),repeat=2)))
    check('0.GP3','Induction inequality examples and comparison in step',all(2**n>=n+1 and (2*n+2)-(n+2)==n for n in range(101)))
    check('0.GP4','Exact attaining error example and safe endpoints',
          [abs(F(5)-F('4.8')),abs(F('4.8')-F('4.7')),abs(F(5)-F('4.7')),F('4.7')-F('.3'),F('4.7')+F('.3')],
          [F('.2'),F('.1'),F('.3'),F('4.4'),F(5)])
    check('0.GL1','Sufficient and minimal strict epsilon thresholds',floor(1/F(1,4))+1==5 and F(1,6)<F(1,4) and F(1,5)<F(1,4) and not F(1,4)<F(1,4))
    check('0.GL2','Finite geometric formula at every tested horizon',all(sum((F(1,2)**t for t in range(T)),F(0))==2*(1-F(1,2)**T) for T in range(50)))
    check('0.GL3','Telescoping formula and first three terms',
          [F(1)-F(1,2),F(1,2)-F(1,3),F(1,3)-F(1,4),sum((F(1,t+1)-F(1,t+2) for t in range(3)),F(0))],
          [F(1,2),F(1,6),F(1,12),F(3,4)])
    check('0.GB1','Finite set bounds and cardinality',[len({-3,1,1,2}),min({-3,1,1,2}),max({-3,1,1,2})],[3,-3,2])
    check('0.GB2','Strict arbitrary-gap example and larger successor',2-F(1,101)>F('1.99') and 2-F(1,100)==F('1.99') and all((2-F(1,n+1))-(2-F(1,n))==F(1,n*(n+1)) for n in range(1,50)))
    values={x:(x-1)**2 for x in [-1,0,1,2]}
    check('0.GB3','Output set, minimum value and all minimizing inputs',
          [set(values.values()),min(values.values()),{x for x,v in values.items() if v==0},{x for x in [0,2] if values[x]==1}],
          [{0,1,4},0,{1},{0,2}])
    check('0.GT1','Missing limit sequence and failing interior neighbourhood',all(0<=1-F(1,n)<1 for n in range(1,50)) and all(-r/2<0 for r in [F(1),F(1,10),F(1,1000)]))
    check('0.GT2','Concrete epsilon-delta output interval',[2*F('.95')+1,2*F('1.05')+1],[F('2.9'),F('3.1')])
    grid=[F(i,10) for i in range(21)]
    check('0.GT3','Factored Lipschitz inequality on bounded pairs and growing counterexample',
          all(abs(x*x-y*y)==abs(x-y)*abs(x+y)<=4*abs(x-y) for x,y in product(grid,repeat=2)) and all((n+1)**2-n*n==2*n+1 for n in range(100)))
    check('0.GR1','Big-O witness constants and exact threshold',all(3*n+4<=7*n for n in range(1,100)) and 3*3+4>4*3 and all(3*n+4<=4*n for n in range(4,100)))
    check('0.GR2','Cumulative and average values at ten thousand trials',
          [100*100,100*10000,F(100),F(100,100),F(100),F(100,10000)],[10000,1000000,F(100),F(1),F(100),F('.01')])
    check('0.GR3','Exact crossover and both tolerance budgets',
          [F(1000,10**6),F(1,1000),1000/F('.01'),1/F('.01')**2,1000/F('.0001'),1/F('.0001')**2],
          [F('.001'),F('.001'),100000,10000,10000000,100000000])

    # All fifty original questions, including newly expanded calculations.
    X={-2,-1,0,1,2,3};A={x for x in X if x*x<=4};B={x for x in X if x>0}
    check('0.S1','Set-builder filtering and both failed subset tests',A=={-2,-1,0,1,2} and B=={1,2,3} and not B<=A and not A<=B)
    A={0,2,4};B={2,3,4};X=set(range(6))
    check('0.S2','Four set operations and union count',[A|B,A&B,A-B,X-A,len(A|B)],[{0,2,3,4},{2,4},{0},{1,3,5},4])
    check('0.S3','Witness and two-input incompatibility',[(0+2),(1+2),0**2>=0],[2,3,True])
    check('0.S4','Negated boundary comparisons',0**2<1 and all(x<=x for x in [F(0),F(1,2),F(1)]))
    check('0.S5','Converse counterexample and original factorization',[(-4)**2>9,-4>3,(F(4)-3)*(F(4)+3)],[True,False,F(7)])
    check('0.S6','Explicit excluding interval for a small nonzero input',F(1,101)<F('.01')<=F(1,100))
    check('0.S7','De Morgan membership including both endpoints',all(not(x>=-1 and x<=2)==(x<-1 or x>2) for x in [F(-2),F(-1),F(0),F(2),F(3)]))
    S={('a','L'),('b','R'),('c','L'),('c','R')};X=['a','b','c'];U=['L','R']
    check('0.S8','Both quantifier orders on the complete safe-pair list',all(any((x,u) in S for u in U) for x in X) and not any(all((x,u) in S for x in X) for u in U))
    check('0.S9','Small actuator counterexample and limiting feasibility',F(-1,4)>=F(-1,2) and not -1>=F(-1,2) and all(-1<=-x<=1 and x-x==0 for x in [F(i,4) for i in range(-4,5)]))
    check('0.F1','Original and repaired domain/codomain properties',{x*x for x in [-2,-1,0,1,2]}=={0,1,4} and len({x*x for x in [0,1,2]})==3)
    check('0.F2','Composition values and sole agreement input',[2*2**2-1,(2*2-1)**2,2*1**2-1,(2*1-1)**2],[7,9,1,1])
    x=F(-1);seq=[]
    for k in range(1,4):x=(x+3)/4;seq.append(x);assert x==1-F(2,4**k)
    check('0.F3','Direct iteration and exact error formula',seq,[F(1,2),F(7,8),F(31,32)])
    check('0.F4','Images and negative preimage branch',(-3)**2==9 and 0**2==0 and F(-3,2)**2==F(9,4))
    check('0.F5','Nonnegative inverse and domain collision',(-1)**2==1**2 and all(F(n)**2>=0 and sqrt(n*n)==n for n in range(20)))
    x=F(0);seq=[]
    for k in range(1,9):x=-x/2+3;seq.append(x);assert x-2==-2*F(-1,2)**k
    check('0.F6','Alternating iterates and exact neighbouring tolerance errors',seq[:3]==[F(3),F(3,2),F(9,4)] and x==F(255,128) and F(1,64)>F(1,100)>F(1,128))
    check('0.F7','Image-intersection singleton counterexample',{-2}&{2}==set() and {(-2)**2}&{2**2}=={4})
    mapping={0:1,1:2,2:2,3:4,4:3};S={0};steps=[]
    for _ in range(3):S=S|{mapping[x] for x in S};steps.append(S)
    check('0.F8','Actual set-growth rounds and monotonicity for all subsets',steps==[{0,1},{0,1,2},{0,1,2}] and all((A|{mapping[x] for x in A})<=(B|{mapping[x] for x in B}) for A in [set(s) for k in range(32) for s in [[i for i in range(5) if k>>i&1]]] for B in [set(s) for k in range(32) for s in [[i for i in range(5) if k>>i&1]]] if A<=B))
    check('0.F9','Fixed-point candidates and failed self-map value',[F(0)/2,F(2)/2+1,-F(0),F(1)/2+1],[F(0),F(2),F(0),F(3,2)])
    check('0.P1','Completed-square identity and unique equality instance',all(x*x+2*x+2==(x+1)**2+1 for x in [F(i,3) for i in range(-12,13)]) and (-1)**2+2*(-1)+2==1)
    check('0.P2','Odd-square integer witness identity',all((2*m+1)**2==2*(2*m*m+2*m)+1 for m in range(-50,51)))
    check('0.P3','Three counterexamples and repaired zero-product/sign alternatives',[F(1,2)**2<F(1,2),0*1==0 and 1!=0,(-1)**2==1**2 and -1!=1],[True,True,True])
    check('0.P4','Arithmetic sum formula, including empty sum',all(sum(range(1,n+1))==F(n*(n+1),2) for n in range(101)))
    check('0.P5','Negative counterexample and factored difference',[(-3)**2,(-3)*(-2),(-2)**2,(2-(-3))*(2+(-3))],[9,6,4,-5])
    for start in [F(0),F(1,4),F(1,2),F(1)]:
        x=start
        for t in range(20):
            assert x==F(1,2)+F(1,2)**t*(start-F(1,2));assert 0<=x<=1;x=x/2+F(1,4)
    check('0.P6','Exact invariant trajectories at four starts',True)
    check('0.P7','Uniqueness distance rearrangement and excluded fixed point',all(d-d/3==2*d/3 for d in [F(0),F(1,10),F(1)]) and F(0) not in [F(1,n) for n in range(1,100)])
    check('0.P8','Exact upper-envelope numbers for a half-unit start',[F(4,5)*F(1,2),F(4,5)**2*F(1,2)],[F(2,5),F(8,25)])
    m={'a':'b','b':'c','c':'b','d':'d'};state='a';states=[]
    for _ in range(5):states.append(state);state=m[state]
    exhaustive=True
    for values in product(range(4),repeat=4):
        mapping=dict(enumerate(values))
        for start in range(4):
            reachable=set(orbit(mapping,start));prefix=[];state=start
            for _ in range(4):prefix.append(state);state=mapping[state]
            exhaustive=exhaustive and reachable==set(prefix)
    check('0.P9','Computed trajectory and complete finite enumeration of all 256 four-state maps',states==['a','b','c','b','c'] and exhaustive)
    check('0.4a','First terms and strict/non-strict cutoffs',[F(3),F(3,2),F(3,3),F(3,4),F(3,30)<F('.1'),F(3,31)<F('.1')],[F(3),F(3,2),F(1),F(3,4),False,True])
    check('0.4b','Four rewards and sharp neighbouring tail budgets',sum((2*F(1,2)**t for t in range(4)),F(0))==F(15,4) and 4*F(1,2)**8>F('.01')>4*F(1,2)**9)
    check('0.4c','Excursion count and arbitrarily delayed permitted drop',F(6)/F('.2')**2==150 and F('2.98')-3==-F(1,2)*F('.2')**2)
    check('0.5a','Finite members, midpoint and increasing successor',all(-2<(x-2)/2<x for x in [F(-3,2),F(0),F(3)]) and all((1-F(1,n+1))-(1-F(1,n))==F(1,n*(n+1)) for n in range(1,100)))
    check('0.5b','Parity values and exact two sample tail suprema',[1+F(1,1),-1+F(1,2),1+F(1,7),1+F(1,9)],[F(2),F(-1,2),F(8,7),F(10,9)])
    matrix=[[0,2],[1,0]]
    check('0.5c','All row maxima and column minima',[min(map(max,matrix)),max(min(matrix[i][j] for i in range(2)) for j in range(2))],[1,0])
    check('0.6a','Explicit interior radius and closure sequence',[min(F(1,2)+1,1-F(1,2))/2,F(1,2)-F(1,4),F(1,2)+F(1,4)],[F(1,4),F(1,4),F(3,4)])
    check('0.6b','Strict improvement on punctured interval and attained zero',all((x/2)**2<x*x for x in [F(1,n) for n in range(1,100)]) and 0**2==0)
    coarse=[F(0),F('.4'),F('.8'),F(1)];dist=lambda x:min(abs(x-g) for g in coarse)
    check('0.6c','Fine-grid lower bound and explicit coarse counterexample',[F('.35')-3*F('.1'),F('.35')-3*dist(F('.2')),2*F('.35')/3],[F('.05'),F('-.25'),F(7,30)])
    check('0.7a','Explicit two-sided growth witnesses',all(2*n*n<=2*n*n+3*n+1<=6*n*n for n in range(1,100)))
    check('0.7b','Certified iteration and operation budgets',[40**2,1600*100,8/F('.1'),80*1000],[1600,160000,80,80000])
    check('0.7c','Finite logarithmic regret estimate and little-o product counterexample',abs(5*log(10000)/100-.460517018598809)<1e-14 and sqrt(10000)*sqrt(10000)==10000)
    check('0.B1','Information and acceptance endpoint intervals',[F('4.7')-F('.2'),F('4.7')+F('.2'),F('4.9')-F('.2'),F('4.9')+F('.2')],[F('4.5'),F('4.9'),F('4.7'),F('5.1')])
    check('0.B2','Robust command thresholds and both extreme successors',[F('1.1')*F('4.8'),5-F('1.1')*F('4.8')-F('.4'),F('1.1')*F('4.8')-1,F('1.1')*F('4.8')-F('.68')+F('.4')],[F('5.28'),F('-.68'),F('4.28'),F(5)])
    e=F('.7');envelope=[]
    for k in range(8):envelope.append(e);assert e==F('.06')+F('.64')/2**k;e=e/2+F('.03')
    check('0.B3','All eight traced envelope values',envelope,[F(s) for s in ['.70','.38','.22','.14','.10','.08','.07','.065']])
    check('0.B4','Exact limiting disturbance boundary and interior feedback',F('1.1')*5-1+F('.5')==5 and F('-.2')*F('2.5')==F('-.5') and F('.9')*F('2.5')==F('2.25'))
    interval=lambda x:(max(F(-1),-1-2*x),min(F(1),1-2*x))
    check('0.1','Command sets at both boundaries and centre',[interval(F(1)),interval(F(-1)),interval(F(0))],[(F(-1),F(-1)),(F(1),F(1)),(F(-1),F(1))])
    vals=[F(s) for s in ['1.8','2.3','1.4','2.4','1.4','2.4','1.4','.4','1.4']]
    def closure(error):
        S={0};rounds=[S]
        while True:
            nxt=S|{x for x in range(9) if any(vals[p]-error-abs(x-p)>=0 for p in S)}
            rounds.append(nxt)
            if nxt==S:return rounds
            S=nxt
    check('0.2','Both complete reachability closures and all new gateway margins',closure(F('.5'))==[{0},{0,1},{0,1,2},{0,1,2}] and closure(F(0))[-1]==set(range(8)) and [vals[p]-F('.5')-abs(3-p) for p in range(3)]==[F('-1.7'),F('-.2'),F('-.1')])
    gamma=F('.9')
    check('0.3','Finite geometric identity including zero discount and weighted result',all(sum((g**t for t in range(T)),F(0))==(1-g**T)/(1-g) for g in [F(0),F(1,2),F(9,10),F(-1,2)] for T in range(20)) and gamma/(1-gamma)**2==90 and gamma/(1-gamma)==9)
    check('0.4','Image inverse, parity terms and common-input trigonometric optimum',all((y/(1-y))/(1+y/(1-y))==y for y in [F(0),F(1,4),F(1,2),F(9,10)]) and [(-1)**t*(1+F(1,t+1)) for t in range(4)]==[F(2),F(-3,2),F(4,3),F(-5,4)] and abs(sin(3.141592653589793/4)+cos(3.141592653589793/4)-sqrt(2))<1e-14)
    check('0.5','Constrained minimizer and sublevel parameter boundaries',F(1,2)**2+F(1,2)**2==F(1,2) and all((a+b)**2+(a-b)**2==2*(a*a+b*b) for a,b in product([F(-1),F(0),F(1,2),F(2)],repeat=2)) and F(1,2)/(1-F(1,2))==1)
    with localcontext() as ctx:
        ctx.prec=60
        b=lambda T:4*Decimal(T).ln()/Decimal(T).sqrt()
        crossing=b(246638)>Decimal('.1')>=b(246639)
    check('0.6','High-precision neighbouring permanent cutoffs, cubic work and six-axis product',crossing and F('.05')*4**3==F('3.2') and 20**6==64000000 and 20**10==10240000000000)

    c0,c1=trig_bounds(F(1),'cos');L0,L1=trig_bounds(F(1),'sin')
    root0,root1=F('0.7390851331'),F('0.7390851333')
    assert trig_bounds(root0,'cos')[0]>root0 and trig_bounds(root1,'cos')[1]<root1
    intervals=[(F(1),F(1))]
    for k in range(1,33):
        lo,hi=intervals[-1]
        intervals.append(round_out(trig_bounds(hi,'cos')[0],trig_bounds(lo,'cos')[1]))
    iter32=intervals[32];iter31=intervals[31]
    assert F('0.73908599959')<=iter32[0]<=iter32[1]<=F('0.73908599970')
    assert iter32[1]-root0<F('0.000001')
    assert root0-iter31[1]>F('0.000001')
    prior86=L0**86*(1-c1)/(1-L0);prior87=L1**87*(1-c0)/(1-L1)
    check('0.7','Rational cosine enclosures, minimal actual iteration and a priori neighbouring certificates',prior86>F('0.000001')>=prior87 and L1<1)

    assert len(checks)==80 and len({r['exercise'] for r in checks})==80
    assert set(sources)=={r['label'] for r in checks}
    h.json_put(BASE+'/arithmetic-check.json',dict(status='passed',source=h.ref(BASE+'/candidates/SafeLearning/primer-basics.html'),
        helper=h.ref(BASE+'/check_math.py'),exercise_checks=checks,exercise_count=80,
        cosine_interval_method='Exact rational alternating Taylor bounds (18/19 terms), rounded out to 20 decimal places at every iteration; endpoint sign brackets for unique fixed point.',
        cosine_iterate32=[str(v) for v in iter32],
        scope='Worked calculations, boundary decisions, algebra instances, complete finite set/graph cases and exact cosine enclosures. Finite checks do not prove universal real claims. Mathematical and pedagogical self-review is separately recorded; no independent agent review or full formal coverage is inferred.'))
    print(dict(status='passed',exercises_with_checks=80,cosine_interval_certificate=True))


if __name__=='__main__':main()
