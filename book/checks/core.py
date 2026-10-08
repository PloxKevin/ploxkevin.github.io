"""Independent exact/numerical checks for the application chapters8–11."""
from fractions import Fraction as F
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[2]
checks = []

def check(key, actual, expected, tolerance=1e-10):
    if isinstance(actual, (tuple, list)):
        ok = len(actual) == len(expected) and all(abs(float(a)-float(b)) <= tolerance
                                                for a,b in zip(actual, expected))
    else:
        ok = abs(float(actual)-float(expected)) <= tolerance
    checks.append(dict(key=key, actual=str(actual), expected=str(expected), passed=ok))
    assert ok, (key, actual, expected)

#8: Model aggregation, constrained optima and exact trajectory accounting.
gamma = F(9,10)
def reward(p, g=gamma): return (2+3*p)/(1-g)
def cost(p, g=gamma): return (F(1,50)+F(9,50)*p)/(1-g)
check('m8-worked-policy', (reward(F(4,9)),cost(F(4,9))), (F(100,3),1))
check('m8-worked-dual-slope',30-F(50,3)*F(9,5),0)
check('m8-b1', (reward(F(1,4)),cost(F(1,4))), (F(55,2),F(13,20)))
check('m8-b2-new', (reward(F(1,6),F(19,20)),cost(F(1,6),F(19,20))), (50,1))
check('m8-b2-reused', cost(F(4,9),F(19,20)),2)
z1=(1-F(2,5))/gamma;z2=(z1-F(1,5))/gamma
check('m8-worked-budget', (z1,z2,gamma**2*z2),(F(2,3),F(14,27),F(21,50)))
check('m8-worked-rejected-cost',F(2,5)+gamma*F(1,5)+gamma**2*F(3,5),F(533,500))
z3=(z2-F(1,2))/gamma
check('m8-b3',(z3,gamma**3*z3,F(2,5)+gamma*F(1,5)+gamma**2*F(1,2)),(F(5,243),F(3,200),F(197,200)))

#9: Exact geometry up to ordinary floating square-root evaluation; KKT certificate.
s=(.2,math.sqrt(6)/5);lam=5/(4*math.sqrt(6));nu=2-1/(4*math.sqrt(6))
check('m9-worked-trust-ellipse',s[0]**2+4*s[1]**2,1)
check('m9-worked-reward',2*s[0]+s[1],(2+math.sqrt(6))/5)
check('m9-b2-kkt',(lam*s[0]+nu,lam*4*s[1]),(2,1))
check('m9-b1-trust-costs',(.5*(.5**2),.5*4*(.5**2)),(.125,.5))
check('m9-b3-remainder-original',-F(1,5)+F(1,5)+F(1,5)*F(7,25),F(7,125))
check('m9-b3-remainder-conservative',-F(1,5)+F(1,5)*F(1,4),-F(3,20))
check('m9-worked-unconstrained',(4/math.sqrt(17),1/(2*math.sqrt(17))),(0.9701425001453319,0.12126781251816648))

#10: Affine worst-case clearance is minimized at an interval endpoint.
def command(y,err,hold): return F(1,10)-(y-err)/hold
for key,y,err,hold,expected in [
    ('m10-worked',F(7,20),F(1,20),F(1,2),-F(1,2)),
    ('m10-b1',F(7,20),F(2,25),F(1,2),-F(11,25)),
    ('m10-b3',F(7,20),F(7,50),F(1,2),-F(8,25)),
]:
    u=command(y,err,hold);check(key+'-command',u,expected)
    check(key+'-terminal',y-err+hold*(u-F(1,10)),0)
check('m10-worked-objective',F(1,2)*(-F(1,2)+F(4,5))**2,F(9,200))
check('m10-worked-reserved-clearance',F(3,10)+F(1,2)*(-F(9,20)-F(1,10)),F(1,40))
check('m10-b2-critical-clearance',F(1,10)*F(1,2),F(1,20))
check('m10-b3-age-error',F(1,20)+F(9,10)*F(1,10),F(7,50))
check('m10-b3-reused-command',F(21,100)+F(1,2)*(-F(1,2)-F(1,10)),-F(9,100))

#11: Exact invariant radii, tightened sets and the average/uniform-error distinction.
for key,err,r in [('m11-worked',F(7,100),F(7,50)),('m11-b1',F(9,100),F(9,50))]:
    check(key+'-invariant-radius',F(1,2)*r+err,r)
    check(key+'-tightened-band',1-r,F(43,50) if key=='m11-worked' else F(41,50))
check('m11-worked-nominal-decrease',F(1,2)**2-1,-F(3,4))
check('m11-b2-error-budget',F(4,25)*(1-F(1,2))-F(1,20),F(3,100))
check('m11-b3-MSE',F(1,200)*F(1,10)**2,F(1,20000))
check('m11-b3-RMSE',math.sqrt(.00005),.007071067811865475)
check('m11-b3-missed-region',.995**200,.36695782172616703)

chapters=[]
for filename,num in [('cmdp.html',8),('policy-optimization.html',9),('barriers.html',10),('lyapunov-mpc.html',11)]:
    path=ROOT/'book/chapters'/filename
    import re
    text=re.sub(r'<[^>]+>',' ',path.read_text())
    chapters.append(dict(file=str(path.relative_to(ROOT)),word_count=len(text.split()),
                         exercises=[f'book-m{num}-b{i}' for i in range(1,4)]))
report=dict(status='passed',chapters=chapters,check_count=len(checks),checks=checks,
            limits='Exact rational calculations and numeric evaluation of explicitly derived formulas. '
                   'The modeling/inequality arguments are reviewed separately; these computations are not universal proofs.')
out=ROOT/'book/review/core.json';out.write_text(json.dumps(report,indent=2)+'\n')
print(len(checks),'core application calculations passed.')
