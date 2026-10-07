"""Independent arithmetic checks for the worked exercises in primers C--E.

Run from the repository root: python qa/applied_primer_math.py
This verifies numerical answers, not the hypotheses of general theorems.
"""
from pathlib import Path
import json
import math
import numpy as np
from scipy import linalg, stats

checks = []


def check(name, actual, expected, tolerance=1e-6):
    a = np.asarray(np.real_if_close(actual), dtype=float)
    b = np.asarray(expected, dtype=float)
    passed = bool(np.allclose(a, b, atol=tolerance, rtol=0))
    checks.append(dict(name=name, actual=a.tolist(), expected=b.tolist(),
                       tolerance=tolerance, passed=passed))


# Each new graded problem has an individually named numerical/algebraic check.
x, p = np.array([0., 2., 4.]), np.array([.5, .25, .25])
mean = p @ x
var = p @ (x - mean) ** 2
check('C.S1 finite law', [sum(p), sum(p[x >= 2]), mean], [1, .5, 1.5])
check('C.S2 variance and affine map', [p @ x**2, var, math.sqrt(var), 3*mean+1, 9*var], [5, 2.75, 1.6583124, 5.5, 24.75])
z = np.array([-1., 0., 1.]); centered = np.vstack((z, z**2 - 2/3))
check('C.S3 covariance', centered @ centered.T / 3, [[2/3, 0], [0, 2/9]])
check('C.S4 conditioning die', [3/6, 3/6, (2/6)/(3/6)], [.5, .5, 2/3])
alarm = .8*.1 + .2*.9
check('C.S5 Bayes', [alarm, .8*.1/alarm], [.26, 4/13])
check('C.S6 total variance', [np.mean([0,4]), np.mean([1,1])+np.var([0,4])], [2,5])
P = np.array([[.8,.2],[.3,.7]])
check('C.S7 two transitions', np.array([1,0]) @ np.linalg.matrix_power(P,2), [.7,.3])
stationary = np.linalg.solve(np.vstack((P.T[0]-[1,0], [1,1])), [0,1])
check('C.S8 stationary law', stationary, [.6,.4])
check('C.S9 copied-data variance', [.2*.8/100,.2*.8/50], [.0016,.0032])
check('C.S10 Gaussian probabilities using supplied four-digit table', [stats.norm.cdf(1), stats.norm.cdf(1)-stats.norm.cdf(-1)], [.8413,.6826], 1e-4)
post_var = 1/(1/4+1)
check('C.S11 posterior', [post_var*3,post_var,post_var+1], [2.4,.8,1.8])
cov = np.array([[1,.5],[.5,4]]); h=np.ones(2)
check('C.S12 chance constraint supplied quantile', [h@cov@h,3+1.64485*math.sqrt(h@cov@h)], [6,7.0290], 5e-5)
check('C.S13 Markov bounds', [min(1,2/8),min(1,2/1)], [.25,1])
check('C.S14 sample size', math.ceil(math.log(40)/.02),185)
check('C.S15 centred uniform', [stats.uniform(0,2).mean(), (1-(-1))/2], [1,1])
check('C.S16 union bound', 1-sum([.01]*3),.97)
check('C.S17 simultaneous sample size', math.ceil(math.log(400)/.02),300)
check('C.S18 telescoping budget', sum(.05/(t*(t+1)) for t in range(1,1001)), .05*(1-1/1001))
check('C.S19 fair future increment', np.mean([-1,1]),0)
check('C.S20 predictable multiplier', [np.mean([-2,2]),np.mean([-1,1]),4/2], [0,0,2])
check('C.S21 look-ahead increment', np.mean(np.array([-1,1])**2),1)
check('C.S22 entropies', [stats.entropy([.5,.5]),stats.entropy([.25,.75])], [.693147,.562335])
pp=np.array([.75,.25]);qq=np.array([.5,.5])
check('C.S23 directional KL', [sum(abs(pp-qq))/2,stats.entropy(pp,qq),stats.entropy(qq,pp)], [.25,.130812,.143841])
check('C.S24 support and Pinsker', [stats.entropy([1,0],[.5,.5]),sum(abs(np.array([1,0])-.5))/2,math.sqrt(math.log(2)/2)], [math.log(2),.5,.588705])
loss=np.array([0,10,100]); masses=np.array([.8,.15,.05]);cdf=np.cumsum(masses)
check('C.S25 quantile atoms', [loss[np.searchsorted(cdf,a)] for a in [.8,.9,.95]], [0,10,10])
check('C.S26 CVaR versus mean', [(.05*100+.05*10)/.1,masses@loss,(masses@loss)/.2], [55,6.5,32.5])
check('C.S27 RU slopes and minimum', [*[1-10*sum(masses[loss>v]) for v in [-1,5,50,101]],10+10*(masses@np.maximum(loss-10,0))], [-9,-1,.5,1,55])
check('C.S28 binomial outcomes', [stats.binom.pmf(2,4,.1),stats.binom.sf(0,4,.1)], [.0486,.3439])
check('C.S29 zero failures',1-.05**(1/100),.029513)
check('C.S30 exchangeable ranks',len([r for r in range(1,21) if r<=18])/20,.9)

state=2;trajectory=[]
for control in [1,0,-1]:
    state=.5*state+control;trajectory.append(state)
check('D.S1 recursion',trajectory,[2,1,-.5])
check('D.S2 closed loop', [4*.25**t for t in range(4)], [4,1,.25,.0625])
check('D.S3 equilibrium slopes and Euler', [-1+2*0,-1+2*1,.1+.2*(-.1+.1**2)], [-1,1,.082])
A=np.diag([.5,-1.2]);initial=np.array([2,1])
check('D.S4 diagonal discrete trajectory', [A@initial,np.linalg.matrix_power(A,2)@initial],[[1,-1.2],[.5,1.44]])
check('D.S5 continuous bound at one second', np.linalg.norm(linalg.expm(np.diag([-1,-2]))@np.array([3,4])) <= 5*math.exp(-1),1)
J=np.array([[.5,10],[0,.5]])
check('D.S6 Jordan formula',np.linalg.matrix_power(J,4)@np.array([0,1]),[10*4*.5**3,.5**4])
check('D.S7 scalar certificate derivative at x=3',2*3*(-2*3),-4*3**2)
check('D.S8 Lyapunov matrix',np.diag([-1,-2]).T+np.diag([-1,-2]),[[-2,0],[0,-4]])
check('D.S9 nonlinear sublevel identity',2*.5*(-.5+.5**3),-2*.5**2*(1-.5**2))
check('D.S10 class K saturation limit sample',1000000/(1+1000000),1,2e-6)
check('D.S11 comparison entry time',math.log(20)/3,.998577)
check('D.S12 filter projection',min(1,2*(1-.9)),.2)
check('D.S13 feedback stability rate at k=3',2-3,-1)
riccati=1+math.sqrt(2)
check('D.S14 continuous Riccati residual and rate',[2*riccati-riccati**2+1,1-riccati],[0,-math.sqrt(2)])
check('D.S15 actuator threshold',[1/2,1/3],[.5,1/3])
check('D.S16 DC response', 1/2,.5)
check('D.S17 frequency response',[abs(1/(2+0j)),abs(1/(2+2j))],[.5,.353553])
check('D.S18 impulse norms',[sum(.5**np.arange(100)),math.sqrt(sum(.25**np.arange(100)))],[2,1.154701])
for v in [-3,-.5,0,.5,3]:
    sat=max(-1,min(v,1));assert 0<=v*sat<=v*v
check('D.S19 saturation samples',1,1)
check('D.S20 worst Lyapunov coefficient',-2+1.6,-.4)
check('D.S21 sector Lyapunov coefficient',-2,-2)
B=np.array([1,0]);A=np.diag([.5,.25])
check('D.S22 controllability rank',np.linalg.matrix_rank(np.column_stack((B,A@B))),1)
check('D.S23 integrator Gramian and energy',[2,2*.5**2],[2,.5])
A=np.diag([-1,-2]);B=np.array([1.,1.]);C=np.array([1.,1.]);T=np.diag([2.,1.])
Az=T@A@np.linalg.inv(T);Bz=T@B;Cz=C@np.linalg.inv(T)
check('D.S24 transfer invariance at s=3',[C@np.linalg.solve(3*np.eye(2)-A,B),Cz@np.linalg.solve(3*np.eye(2)-Az,Bz)],[.45,.45])
check('D.S25 one-step optimisation',[-1,2-1,(-1)**2+(2-1)**2],[-1,1,2])
Q=np.array([[2.,1.],[1.,2.]]);u=np.linalg.solve(Q,[-3,-3])
check('D.S26 joint optimum cross-check',[*u,u@u+(3+sum(u))**2],[-1,-1,3])
check('D.S27 terminal feedback endpoints',[-.5+.5,.5-.5],[0,0])

means=np.array([.8,.6,.3]);choices=np.array([0,1,2,1]);regrets=max(means)-means[choices]
check('E.S1 regret',[sum(regrets),np.mean(regrets),max(means)-means[2]],[.9,.225,.5])
check('E.S2 reward UCB and safety LCB',[.5+.2,.6+.05,.3-.4,.2-.1],[.7,.65,-.1,.1])
reward=np.array([[1,0],[0,1]])
check('E.S3 static/dynamic regret',[max(reward.sum(axis=1))-reward[0].sum(),reward.max(axis=0).sum()-reward[0].sum()],[0,1])
check('E.S4 returns',[2+.5*4,4+.5*0],[4,4])
check('E.S5 nested averages',[1+.5*(.75*4),.6*(1+.5*(.75*4))+.4*1],[2.5,1.9])
check('E.S6 expected violations',[.01*100,1],[1,1])
check('E.S7 one-state value',2/(1-.5),4)
values=np.linalg.solve(np.eye(2)-.5*np.array([[0,1],[1,0]]),[1,0])
check('E.S8 cycle values and advantage',[*values,.5*values[0]-values[0]],[4/3,2/3,-2/3])
check('E.S9 constrained occupancy',[2*.4/(1-.8),.4/(1-.8)],[4,2])
v=0;iterates=[]
for _ in range(3):v=2+.5*v;iterates.append(v)
check('E.S10 value iteration',iterates,[2,3,3.5])
check('E.S11 residual bound',[.03/(1-.9),.1*(1-.9)],[.3,.01])
check('E.S12 transient undiscounted value',1/(1-.5),2)
p=.25;scores=np.array([1-p,-p]);probs=np.array([p,1-p])
check('E.S13 direct gradient and scores',[4*p,4*p*(1-p),*scores,probs@scores],[1,.75,.75,-.25,0])
advantages=np.array([3,-1])
check('E.S14 baseline gradient',probs@(advantages*scores),.75)
F=np.diag([4,1]);g=np.array([2,1]);direction=np.linalg.solve(F,g);delta=math.sqrt(.1/(g@direction))*direction
check('E.S15 natural step', [*delta,.5*delta@F@delta,g@delta],[.111803,.223607,.05,.447214])
target=1+.9*2
check('E.S16 Q update',[target,target-.5,.5+.2*(target-.5)],[2.8,2.3,.96])
weights=np.exp([0,math.log(3)])
check('E.S17 entropy solution',[*(weights/sum(weights)),math.log(sum(weights))],[.25,.75,1.386294])
check('E.S18 mixture variance',[np.mean([0,2]),np.mean([1,1])+np.var([0,2])],[1,2])
W=np.array([2,-1]);vv=[W@np.array(xx)+.5 for xx in [(1,3),(2,1)]]
check('E.S19 forward pass',[*vv,*np.maximum(vv,0)],[-.5,3.5,0,3.5])
def loss(params):
    w,a,b,x=params
    return .5*(w*max(0,a*x+b)-1)**2
base=np.array([3.,2.,-1.,1.]);eps=1e-5;finite=[]
for j in range(4):
    d=np.eye(4)[j]*eps;finite.append((loss(base+d)-loss(base-d))/(2*eps))
check('E.S20 chain rule finite differences',finite,[2,6,6,12],1e-5)
W1=np.array([[1.],[-1.]]);W2=np.array([[1.,-1.]])
check('E.S21 product Lipschitz bound',np.linalg.norm(W1,2)*np.linalg.norm(W2,2),2)
conv=np.array([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]])
check('E.S22 convolution',conv@np.array([1,2,3,4]),[-1,-1,-1])
check('E.S23 residual constants',[abs(1+.2),1+abs(.2),abs(1-.8),1+abs(-.8)],[1.2,1.2,.2,1.8])
z=0;zs=[]
for _ in range(3):z=.5*z+2;zs.append(z)
check('E.S24 equilibrium residual',[*zs,abs(.5*z+2-z)/(1-.5)],[2,3,3.5,.5])
check('E.S25 logit gaps',[3-1-2*.4,3-0-2*.4],[1.2,2.2])
check('E.S26 scalar boundary radius',[abs(2*1+1)/2,abs(1-(-.5))],[1.5,1.5])
check('E.S27 radius and accuracy bounds',[1/(math.sqrt(2)*2),50/100,(80-10)/100],[.353553,.5,.7])
check('C.R1 complement',1-.15,.85)
check('C.R2 weighted mean',np.mean([2,6,6,6]),5)
check('C.R3 outer product',np.outer([1,2],[1,2]),[[1,2],[2,4]])
check('D.R1 fixed point',1/(1-.5),2)
check('D.R2 derivative at zero',3*(-2),-6)
check('D.R3 quadratic form',np.array([1,-2])@np.diag([1,2])@np.array([1,-2]),9)
check('E.R1 expectation',.25*4+.75*0,1)
check('E.R2 discounted return',2/(1-.5),4)
check('E.R3 partial derivatives by finite differences',
      [((3+eps)*2-(3-eps)*2)/(2*eps),(3*(2+eps)-3*(2-eps))/(2*eps)],[2,3])

# Recompute the substantive numbers in all original cumulative exercises too.
check('Original C.1 SE and zero failures',[math.sqrt(.07*.93/200),1-.05**(1/200)],[.0180,.0149],5e-5)
check('Original C.2 alarm and threshold',[.018/(.018+.0098),1-.99**500,stats.norm.ppf(1-.0001/2)],[.648,.993,3.89],.001)
pv=1/17;pm=16*.9/17
check('Original C.3 posterior',[pm,pv,stats.norm.cdf((.5-pm)/math.sqrt(pv)),pm-2*math.sqrt(pv)],[.847,.0588,.076,.362],.001)
check('Original C.4 sample sizes',[math.ceil(.25/(.01*.05**2)),math.ceil(math.log(200)/(.005))],[10000,1060])
p=np.array([.6,.3,.1]);q=np.array([.4,.4,.2])
check('Original C.5 KLs',[stats.entropy(p,q),stats.entropy(q,p),sum(abs(p-q))/2],[.0877,.0915,.2],5e-5)
check('Original C.6 Gaussian CVaR',.8+math.sqrt(4.96)*stats.norm.pdf(stats.norm.ppf(.9))/.1,4.71,.005)
vc=18*2/(20**2*21)
check('Original C.7 coverage randomness',[stats.beta.cdf(.8,18,2),math.sqrt(vc+(0.9*.1-vc)/2000)],[.083,.0658],.0005)
up=np.array([[0,1],[10,-.1]]);down=np.array([[0,1],[-10,-.1]])
check('Original D.1 upright eigenvalues',np.sort(np.linalg.eigvals(up)),[-3.213,3.113],.001)
check('Original D.1 Euler modulus',abs(np.linalg.eigvals(np.eye(2)+.1*down)[0]),1.044,.001)
M=np.array([[0,-.5],[1,1]])
check('Original D.2 trace determinant',[np.trace(M),np.linalg.det(M)],[1,.5])
A=np.array([[0,1],[-1,-1]])
P=linalg.solve_continuous_lyapunov(A.T,-np.eye(2))
check('Original D.3 Lyapunov matrix',P,[[1.5,.5],[.5,1]])
check('Original D.4 affine comparison',.5+2.5*math.exp(-2),.838,.001)
pd=linalg.solve_discrete_are(np.array([[1.2]]),np.ones((1,1)),np.ones((1,1)),np.ones((1,1)))[0,0]
gain=1.2*pd/(1+pd)
check('Original D.5 DARE and gain interval',[pd,gain,1.2-gain,.2/gain,2.2/gain],[1.952,.794,.406,.252,2.772],.001)
check('Original D.6 storage quadratic coefficients', [1.8*.8**2-1.8+.36,2*1.8*.8,1.8-9],[-.288,2.88,-7.2])
check('Original D.7 circle boundary',.6*(-1-.8)/(1.64+1.6),-1/3)
check('Original D.8 viability and tube',[.3/(1.5-1),.2/(1-.4),2-.2/(1-.4),1-.6*.2/(1-.4)],[.6,1/3,5/3,.8])
check('Original E.1 horizon and seconds',[math.ceil(math.log(.01)/math.log(.95)),-.1/math.log(.95)],[90,1.95],.005)
N=np.linalg.inv(np.eye(2)-.9*np.full((2,2),.5))
check('Original E.2 fundamental matrix',N,[[5.5,4.5],[4.5,5.5]])
check('Original E.3 feasible discount',4.5/5.5,9/11)
def baseline_var(b):
    gv=np.array([(1-b)*.2,b*.8]);return np.array([.8,.2])@(gv-.16)**2
check('Original E.4 baseline variances',[baseline_var(0),baseline_var(.8),baseline_var(.2)],[.0064,.0576,0])
check('Original E.5 performance difference',10*(.1*(-1.9)+.9*1.1),8)
check('Original E.6 GAE',[.04+.45*(.12+.45*.2),.04+.9*.12+.81*.2],[.1345,.31])
check('Original E.7 soft values',[.5*np.logaddexp(0,2),np.logaddexp(0,1)],[1.0635,1.3133],5e-5)
check('Original E.8 radii',[1/math.sqrt(10),math.sqrt(8),.5/math.sqrt(10)],[.316,2.83,.158],.005)

# Selected original narrative examples, in addition to every cumulative exercise.
check('Original C excursion mean',.5*(1**2/2),.25)
check('Original C alarm base rate',.95*.01/(.95*.01+.05*.99),.161,.001)
check('Original C policy averaging',[.7*2+.3*10,.9*2+.1*10],[4.4,2.8])
check('Original C mixture tails',[
    .8*2*stats.norm.sf(10)+.2*2*stats.norm.sf(5/3),
    2*stats.norm.sf(5/math.sqrt(2)),
    .8*2*stats.norm.sf(2)+.2*2*stats.norm.sf(1/3),
    2*stats.norm.sf(1/math.sqrt(2))], [.019,.0004,.18,.48],.005)
check('Original C Bayesian zero failures',[stats.beta.mean(1,11),stats.beta.sf(.2,1,11)],[.083,.086],.0005)
check('Original C nested mass',.95*.99,.9405)
P=np.array([[.9,.1],[.5,.5]])
check('Original C Markov transient',np.array([0,1])@np.linalg.matrix_power(P,4),[.812,.188])
check('Original C transient fundamental matrix',np.linalg.inv(np.eye(2)-np.array([[.5,.3],[.2,.4]])),[[2.5,1.25],[5/6,25/12]])
check('Original C stationary noise',[.01/(1-.9**2),math.sqrt(.01/(1-.9**2))],[.0526,.229],.0005)
check('Original C truncated return',.99**500/(1-.99),.657,.001)
check('Original C concentration sample count',math.ceil(math.log(40)/(2*.05**2)),738)
bernoulli_kl=stats.entropy([.03,.97],[.01,.99])
check('Original C rare-event tail bounds',[math.exp(-1000*bernoulli_kl),stats.binom.sf(29,1000,.01)],[1.9e-6,2e-7],5e-8)
check('Original C simultaneous Gaussian radii',[stats.norm.ppf(1-.05/(2*100)),stats.norm.ppf(1-.05/(2*10000))],[3.48,4.56],.005)
check('Original C entropy in nats and bits',[stats.entropy([.7,.2,.1]),stats.entropy([.7,.2,.1],base=2)],[.802,1.157],.0005)
check('Original C Gaussian information',[.5*math.log(25),.5*math.log(21),.5*math.log(9)],[1.609,1.522,1.099],.0005)
check('Original C CVaR split tail',(.05*1+.1*5)/.15,3.67,.005)
scenario_n=next(n for n in range(1,300) if stats.binom.cdf(1,n,.05)<.001)
check('Original C scenario first sample size',scenario_n,181)
check('Original C exact success lower limit',stats.beta.ppf(.05,95,6),.898,.001)
check('Original C smoothing limit',.5*stats.norm.ppf(.001**.01),.75,.01)
check('Original C change-trigger quantile',stats.norm.ppf(1-2.5e-5),4.06,.005)
s=.5;ss=[]
for _ in range(5):s=1.1*s-.1*s**3;ss.append(s)
check('Original D Parseval scalar iterates',ss,[.5375,.5757,.6142,.6525,.6899],5e-5)
check('Original D Euler exact sampling',[math.exp(-.1),math.exp(-2.5)],[.9048,.082],.0005)
check('Original D tanh local sector and slope',[math.tanh(2)/2,1/math.cosh(2)**2],[.482,.0707],.0005)
check('Original D circle/Popov frequency',[math.sqrt(2+3*math.sqrt(2)),9+6*math.sqrt(2)],[2.50,17.5],.02)
Acl=np.array([[0.,1.],[-2.,-3.]])
P=linalg.solve_continuous_lyapunov(Acl.T,-np.eye(2));K=np.array([3.,3.])
check('Original D explorer Lyapunov matrix',P,[[1.25,.25],[.25,.25]])
check('Original D explorer transient and ellipse',[max(np.linalg.eigvalsh(Acl+Acl.T)),4/(K@np.linalg.solve(P,K))],[.16,.111],.003)
check('Original E UCB1',[.6+math.sqrt(2*math.log(12)/10),.5+math.sqrt(2*math.log(12)/2)],[1.305,2.076],.001)
def expected_improvement(mean,sigma,incumbent):
    gap=mean-incumbent;z=gap/sigma
    return gap*stats.norm.cdf(z)+sigma*stats.norm.pdf(z)
check('Original E expected improvement',[expected_improvement(.8,.3,1),expected_improvement(1.05,.05,1)],[.0453,.0542],5e-5)
check('Original E running policy values',np.linalg.solve(np.eye(2)-.9*np.full((2,2),.5),[.5,1]),[7.25,7.75])
check('Original E GAE worked example',.35+.72*(-.6+.72),.436,.0005)
check('Original E softmax temperatures',[np.logaddexp.reduce([1,2,4]),.5*np.logaddexp.reduce(np.array([1,2,4])/.5),5*np.logaddexp.reduce(np.array([1,2,4])/5)],[4.170,4.010,7.986],.0005)
check('Original E ensemble disagreements',[np.var([1,1.2,.8]),np.var([1,2,-.5])],[.027,1.056],.0005)
z=0;zz=[]
for _ in range(5):z=math.tanh(.5*z+1);zz.append(z)
check('Original E equilibrium tanh iterates',zz,[.7616,.8811,.8938,.8951,.8952],.0001)
logits=np.array([2.,.5,1.2]);probs=np.exp(logits-np.max(logits));probs/=sum(probs)
check('Original E logit probabilities',probs,[.598,.133,.269],.001)
check('Original E scaled network margin',abs(2*(.5+2.5-1)-1)/(2*math.sqrt(10)),.474,.001)

out=Path(__file__).resolve().parents[1]/'reports/learning-review/primers-applied-math.json'
out.write_text(json.dumps(dict(check_count=len(checks),all_passed=all(c['passed'] for c in checks),checks=checks),indent=2)+'\n')
failed=[c['name'] for c in checks if not c['passed']]
print(json.dumps(dict(check_count=len(checks),all_passed=not failed,failed=failed,report=str(out)),indent=2))
assert not failed, failed
