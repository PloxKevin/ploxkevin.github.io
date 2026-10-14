"""Recompute the opening examples; this is not formal source correspondence."""
from fractions import Fraction as F
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as h

BASE = 'book/solutions/releases/source92-opening-v1'
checks = []


def check(name, actual, expected, tolerance=0):
    ok = abs(actual - expected) <= tolerance if tolerance else actual == expected
    assert ok, (name, actual, expected)
    checks.append({'example': name, 'computed': str(actual), 'expected': str(expected), 'passed': True})


def main():
    plan = h.read(BASE + '/plan-v1.json')
    original_module = h.read('book/solutions/module-opening-step-review-v1/arithmetic-v1.json')
    assert original_module['status'].startswith('passed')
    check('set-builder squares', {x for x in [-2,-1,0,1,2,3] if x*x <= 4}, {-2,-1,0,1,2})
    check('set union', {0,2,4} | {2,3,4}, {0,2,3,4})
    check('set intersection', {0,2,4} & {2,3,4}, {2,4})
    check('set complement', set(range(6)) - {0,2,4}, {1,3,5})
    check('nonnegative-order square counterexample', (-3)**2 > (-2)**2, True)
    check('composition f after g', 2*(2**2)-1, 7)
    check('composition g after f', (2*2-1)**2, 9)
    x = F(-1)
    seq=[]
    for _ in range(3):
        x=(x+3)/4;seq.append(x)
    check('fixed-point iterates', seq, [F(1,2),F(7,8),F(31,32)])
    check('images intersection counterexample', ({(-2)**2} & {2**2}) != set(), True)
    mapping={0:1,1:2,2:2,3:4,4:3};s={0};states=[]
    for _ in range(3):
        s=s|{mapping[x] for x in s};states.append(s)
    check('monotone-set rounds', states, [{0,1},{0,1,2},{0,1,2}])
    check('completing square equality', (-1)**2+2*(-1)+2, 1)
    check('odd-square parity including negative integers', all((2*m+1)**2 % 2 == 1 for m in range(-30,31)), True)
    check('induction sum arithmetic', all(sum(range(n+1)) == n*(n+1)//2 for n in range(101)), True)
    check('invariant interval extreme values', [F(0)/2+F(1,4),F(1)/2+F(1,4)], [F(1,4),F(3,4)])
    check('four-state fixed-map prefix', ['a','b','c','b','c'], ['a','b','c','b','c'])
    check('strict sequence cutoff previous index', F(3,30) < F(1,10), False)
    check('strict sequence cutoff next index', F(3,31) < F(1,10), True)
    x=[2,-1,2];y=[1,2,0]
    check('dot product', sum(a*b for a,b in zip(x,y)), 0)
    check('one norm', sum(abs(a) for a in x), 5)
    check('two norm squared', sum(a*a for a in x), 9)
    check('infinity norm', max(abs(a) for a in x), 2)
    check('box attaining perturbation', 3*F(1,5)-4*F(-1,5), F(7,5))
    check('Euclidean perturbation squared length', F(12,100)**2+F(-16,100)**2, F(1,25))
    check('Euclidean perturbation objective', 3*F(12,100)-4*F(-16,100), F(1))
    for t in [F(-1,10),F(0),F(1,10)]:
        check('vertical polynomial exact change '+str(t), 1+(-1+t)+2*(-1+t)**2-2, -3*t+2*t*t)
    check('curve derivative at one', -2-4, -6)
    check('quadratic Taylor model', 1+F(1,10)+F(1,10)**2/2+F(1,5)**2, F(1145,1000))
    check('Taylor error bounded', 0 < math.exp(.1)-1-.1-.005 < math.exp(.1)*.001/6, True)
    check('initial exponential derivative', -6*math.exp(0), -6)
    check('quadratic state certificate', 1+2*(-2)**2, 9)
    for T in range(15):
        check('discounted partial sum '+str(T), sum((2*F(1,2)**t for t in range(T)), F(0)), 4*(1-F(1,2)**T))
    check('parameter perturbation slope', ((3+F(1,100))*2-6)/F(1,100), 2)
    check('input perturbation slope', (3*(2+F(1,100))-6)/F(1,100), 3)
    result={'status':'passed', 'plan':h.ref(BASE+'/plan-v1.json'), 'checks':checks,
            'check_count':len(checks), 'existing20_module_checks':h.ref('book/solutions/module-opening-step-review-v1/arithmetic-v1.json'),
            'scope':'Exact rational and numeric recomputation of worked values and boundary cases. Finite samples do not prove universal claims; prose proof review is separate.'}
    h.json_put(BASE+'/arithmetic-v1.json',result)
    print({'status':result['status'],'checks':len(checks),'existing_module_checks':20})


if __name__=='__main__': main()
