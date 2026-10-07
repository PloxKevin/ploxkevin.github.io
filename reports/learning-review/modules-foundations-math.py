"""Independent arithmetic checks for new Module 1--7 practice (standard library only)."""
from fractions import Fraction as F
from pathlib import Path
import json, math

checks=[]
def close(exercise, label, actual, expected, tol=1e-10):
    assert math.isclose(float(actual),float(expected),rel_tol=tol,abs_tol=tol),(exercise,label,actual,expected)
    checks.append(dict(exercise=exercise,calculation=label,value=float(actual),expected=float(expected),passed=True))

def eq(exercise,label,actual,expected):
    assert actual==expected,(exercise,label,actual,expected)
    checks.append(dict(exercise=exercise,calculation=label,value=actual,expected=expected,passed=True))

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def tr(a):return [list(x) for x in zip(*a)]

close('1.P1','h(1.5)',4-1.5**2,1.75)
close('1.P2','expected unsafe steps',.9*0+.1*5,.5)
close('1.P3','independent four-step safe probability',.99**4,.96059601)
close('1.P5','per-step budget',.02/20,.001)
close('1.P6','mean cost',.8*0+.15*2+.05*10,.8)
close('1.P6','worst-ten-percent tail cost',(.05*10+.05*2)/.1,6)
close('1.P6','variational CVaR at quantile',2+.05*8/.1,6)
close('1.P8','logit radius',.6/(2*math.sqrt(2)),.21213203435596426)
close('1.P10','discounted certain future failure',.9**50/(1-.9),.0515377520732012)
eq('1.P11','first unsafe integer time',next(t for t in range(200) if F(t,100)>1),101)
close('1.P12','smallest robust invariant radius',.1/(1-.5),.2)

close('2.P1','active KKT multiplier',-2*(1-2),2)
eq('2.P2','negative-direction quadratic form',mul(mul([[1,-1]],[[1,2],[2,1]]),[[1],[-1]])[0][0],-2)
close('2.P3','Schur threshold',2*2/1,4)
close('2.P5','scalar Stein solution',1/(1-.8**2),F(25,9))
close('2.P7','epigraph minimum at (3,4)',3**2+4**2,25)
close('2.P8','output energy upper bound',4*3,12)
close('2.P9','dual optimum',2-2**2/4,1)
close('2.P11','network slope bound',3*2,6)
close('2.P11','network squared bound',(3*2)**2,36)
a=[[F(1,2),2],[0,F(1,2)]]
p=[[F(4,3),F(16,9)],[F(16,9),F(356,27)]]
apa=mul(mul(tr(a),p),a)
eq('2.P12','Stein residual',[float(apa[i][j]-p[i][j]) for i in range(2) for j in range(2)],[-1.0,0.0,0.0,-1.0])
close('2.P12','positive certificate determinant',p[0][0]*p[1][1]-p[0][1]**2,F(1168,81))

close('3.P1','RKHS squared norm',1-.5-.5+1,1)
close('3.P2','observed posterior mean',2/1.25,1.6)
close('3.P2','observed posterior variance',1-1/1.25,.2)
close('3.P2','other posterior mean',.5*2/1.25,.8)
close('3.P2','other posterior variance',1-.5**2/1.25,.8)
close('3.P3','lower confidence endpoint',1-3*math.sqrt(.04),.4)
close('3.P5','power function',math.sqrt(1-.6**2),.8)
close('3.P5','noise-free norm error',2*math.sqrt(1-.6**2),1.6)
close('3.P6','latent variance after 3 repeats',1-3/(3+1),.25)
close('3.P7','information gain in nats',.5*math.log((1+1.5)*(1+.5)),.6608779199911597)
beta=2+.1/math.sqrt(.04)*math.sqrt(3+2*math.log(20))
close('3.P8','data-dependent beta',beta,3.499288543535565)
close('3.P8','half-width',beta*.2,.6998577087071131)
close('3.P9','minimum squared norm at correlation .99',2/(1-.99),200)
close('3.P10','misspecification bound',.05+(2+.05*math.sqrt(16/.25))*.1,.29)
close('3.P11','telescoping 1000-round risk allocation',sum(1/(t*(t+1)) for t in range(1,1001)),1-1/1001)
m=[[F(3,2),F(1,2)],[F(1,2),F(3,2)]]
v=[[F(3,8)],[-F(1,8)]]
eq('3.P12','variance solve residual',mul(m,v),[[F(1,2)],[0]])
close('3.P12','query latent variance',1-F(1,2)*v[0][0],F(13,16))

close('4.P2','Lipschitz radius',(.6-.1)/2,.25)
eq('4.P3','potential maximizers',[k for k,l,u in [('a',.4,.8),('b',.6,.7),('c',.2,.5)] if u>=.6],['a','b'])
eq('4.P5','intersected interval',[max(.2,.4),min(.8,1)],[.4,.8])
eq('4.P6','expander from distance calculation',[x for x,u in [(0,1.4),(1,1.2)] if u-abs(2-x)>=0],[1])
values={0:F(11,10),1:F(11,10),2:F(1,10),3:F(11,10)}
sets=[{0}]
while True:
    old=sets[-1]
    new=old|{x for x in values if any(values[z]-abs(x-z)>=0 for z in old)}
    sets.append(new)
    if new==old:break
eq('4.P8','reachable iterates',[sorted(s) for s in sets],[[0],[0,1],[0,1,2],[0,1,2]])
close('4.P10','cumulative regret',sum(5-x for x in [2,3,4,3]),8)
close('4.P10','simple regret',5-4.8,.2)
close('4.P11','recommendation gap bound',1.10-1.02,.08)
close('4.P12','continuum margin',.12-2*.05,.02)

close('5.P1','cone radius',(.7-.1-.2)/2,.2)
close('5.P3','conservative radius',.3/3,.1)
eq('5.P4','two-constraint intersection',[max(.1,.3),min(.5,.8)],[.3,.5])
close('5.P5','first ball radius',.35-.05-.1,.2)
close('5.P5','second ball radius',.45-.05-.1,.3)
beta=1+.2/math.sqrt(.04)*math.sqrt(2+2*math.log(10))
close('5.P7','Real-beta multiplier',beta,3.5700525648297723)
close('5.P7','lower band endpoint',.5-.1*beta,.14299474351702274)
close('5.P8','drift-aware lower bound',.8-.1-2*.2-.05*3,.15)
b=[[.2,-.1],[-.3,.1]]
close('5.P10','each constraint chooses a witness',min(max(row) for row in b),.1)
close('5.P10','one shared witness',max(min(b[i][j] for i in range(2)) for j in range(2)),-.1)

close('6.P1','minimum sampled trajectory margin',min(1-abs(x) for x in [0,.3,.9,.4]),.1)
close('6.P2','backup radius',.6/2-.05,.25)
close('6.P2','transferred backup margin',.6-2*(abs(.4-.2)+.05),.1)
close('6.P3','motion allowance',3*.02,.06)
eq('6.P4','six-dimensional joint grid',100*10**6,100000000)
close('6.P8','three-function total failure bound',3*.01,.03)
close('6.P11','maximum sample interval',(.3/2-.1)/5,.01)
close('6.P11','delay-adjusted maximum interval',(.3/2-.1)/5-.004,.006)

close('7.P2','viable fraction',3/5,.6)
close('7.P3','time-three failure return',-20*.9**3,-14.58)
successors={'A':{'A','B'},'B':{'C'},'C':{'F'},'D':{'D'}}
sets=[set(successors)]
while True:
    old=sets[-1];new={x for x in old if successors[x]&old};sets.append(new)
    if old==new:break
eq('7.P5','viability pruning iterates',[sorted(s) for s in sets],[['A','B','C','D'],['A','B','D'],['A','D'],['A','D']])
close('7.P6','safe self-loop value',1/(1-.5),2)
close('7.P6','penalty at unsafe/safe tie',(4-2)/.5,4)
close('7.P7','safe uniform entropy',math.log(3),1.0986122886681098)
close('7.P7','unsafe uniform entropy',math.log(4),1.3862943611198906)
close('7.P10','doomed return upper bound',sum(.9**t for t in range(3))-20*.9**2,-13.49)
close('7.P11','Bellman max-norm error bound',.002/(1-.95),.04)
close('7.P12','50-step critical-action risk bound',50*3*.002,.3)

report=dict(scope='Recomputed numerical results in all seven new graded banks. Proof-only statements reviewed separately in content audit.',checks=checks,count=len(checks),all_passed=all(c['passed'] for c in checks))
Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2,default=float)+'\n')
print(json.dumps(dict(count=len(checks),all_passed=report['all_passed'])))
