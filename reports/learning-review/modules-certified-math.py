#!/usr/bin/env python3
"""Independent arithmetic checks for the 48 new certified-network exercises.
Run from the repository root. Pure proof/assumption cases are reviewed separately.
"""
import json, math
from pathlib import Path
import numpy as np
checks=[]
def check(page,ex,label,actual,expected,tol=1e-9):
 a=np.asarray(actual,dtype=float);e=np.asarray(expected,dtype=float)
 ok=bool(np.allclose(a,e,rtol=tol,atol=tol))
 checks.append(dict(page=page,exercise=ex,label=label,actual=a.tolist(),expected=e.tolist(),passed=ok))
 assert ok,(page,ex,label,a,e)
def c(page,level,num,label,a,e,tol=1e-9):check(page,f'practice-{level}-{num}',label,a,e,tol)
def norm(x):return float(np.linalg.norm(x,2))
def relu(x):return np.maximum(x,0)
f='lipsdp.html'
c(f,'easy',1,'Euclidean radius',.6/(2*np.sqrt(2)),.212132034355964)
c(f,'easy',1,'infinity radius',.6/(2*np.sqrt(6)),.122474487139159)
W0=np.diag([3,1]);W1=np.array([[0,2]])
c(f,'easy',2,'product bound',norm(W0)*norm(W1),6)
c(f,'easy',2,'active output direction',norm(W1@W0),2)
c(f,'easy',3,'scalar QC values',[2*w*(2-w) for w in [1,3,-1]],[2,-6,-6])
c(f,'easy',4,'square root and conflicting lower bound',[np.sqrt(9/4),1.6>np.sqrt(9/4)],[1.5,1])
M=np.array([[-36,12],[12,-4]])
c(f,'medium',1,'negative Gram factor',M,-4*np.outer([3,-1],[3,-1]))
c(f,'medium',1,'eigenvalues and gain',list(np.linalg.eigvalsh(M))+[6],[-40,0,6])
u=np.array([2,-2]);w=np.array([1,-.5]);T=np.diag([3,2])
c(f,'medium',2,'weighted QC',2*w@T@(u-w),9)
W0=np.array([[1],[-1]]);W1=np.array([[1,1]])
c(f,'medium',3,'product and loop bound',[norm(W0)*norm(W1),.5*norm(W1@W0)+.5*norm(W1)*norm(W0)],[2,1])
c(f,'medium',4,'weighted chain coefficients',[4*1.5**2,1*2**2],[9,4])
for b,L in [(0,1),(1,2)]:
 slopes=[]
 for x in [-2,-.5,.5,2]:slopes.append(int(x+b>0)+int(-x+b>0))
 c(f,'hard',1,f'maximum reachable slope with bias {b}',max(slopes),L)
v=np.array([0,2]);vbar=np.array([-1,0]);u=v-vbar;w=relu(v)-relu(vbar);T=np.array([[1,-1],[-1,1]])
c(f,'hard',2,'PSD coupled multiplier eigenvalues',np.linalg.eigvalsh(T),[0,2])
c(f,'hard',2,'invalid coupled and valid diagonal QC',[2*w@T@(u-w),2*w@(u-w)],[-4,0])
c(f,'hard',3,'infeasible numerical eigenvalues',np.linalg.eigvalsh([[-1,1.1],[1.1,-1]]),[-2.1,.1])
c(f,'hard',3,'strict numerical eigenvalues',np.linalg.eigvalsh([[-1,.9],[.9,-1]]),[-1.9,-.1])
c(f,'hard',3,'validated perturbation margin',-.1+.04,-.06)
P=np.array([[1,1,0],[0,1,1]])/2
c(f,'hard',4,'pooling singular values squared',np.linalg.eigvalsh(P@P.T),[.25,.75])
c(f,'hard',4,'pooling attaining vector squared ratio',norm(P@np.array([1,2,1]))**2/norm(np.array([1,2,1]))**2,.75)
f='lipschitz-by-design.html'
c(f,'easy',1,'estimated and upper normalization',[3/2.5,3/np.sqrt(10)],[1.2,.948683298050514])
A=np.array([[0,1],[-1,0]]);Q=(np.eye(2)-A)@np.linalg.inv(np.eye(2)+A)
c(f,'easy',2,'Cayley rotation',Q,[[0,-1],[1,0]])
c(f,'easy',2,'rotated vector',Q@np.array([3,-4]),[4,3])
W=np.array([[1],[0]])
c(f,'easy',3,'forward Gram',W.T@W,[[1]])
c(f,'easy',3,'backward Gram',W@W.T,[[1,0],[0,0]])
c(f,'easy',3,'lost output gradient',W.T@np.array([0,2]),[0])
c(f,'easy',4,'raw bound and radius',[.8*4,.4/(np.sqrt(2)*.8*4)],[3.2,.0883883476483184])
P=np.array([[1,1],[0,1]]);T=np.diag(np.sum(np.abs(P.T@P),axis=1));D=np.diag(1/np.sqrt(np.diag(T)))
c(f,'medium',1,'AOL T',T,[[2,0],[0,3]])
c(f,'medium',1,'AOL squared singular values',np.linalg.eigvalsh(D@P.T@P@D),[1/6,1])
c(f,'medium',2,'SLL active slopes',[1-2*2**2/t for t in [4,2]],[-1,-3])
U=np.sqrt(2)/2*.8;Y=np.sqrt(2)*.6*2
c(f,'medium',3,'scalar sandwich coefficients',[U,Y,U*Y],[2*np.sqrt(2)/5,6*np.sqrt(2)/5,24/25])
c(f,'medium',3,'multiplier residuals',[2*l-Y**2-l*l*U**2 for l in [4,2]],[0,-4/25])
A=np.array([[0,1],[0,0]]);B=np.array([[0],[1]]);X=B@B.T+A@B@B.T@A.T
c(f,'medium',4,'nilpotent Gramian',X,np.eye(2))
c(f,'medium',4,'Gramian recursion',A@X@A.T+B@B.T,X)
c(f,'hard',1,'true example difference identity',[relu(x)-relu(-x) for x in [-2,-1,0,1,2]],[-2,-1,0,1,2])
W0=np.diag([4,.25]);W1=np.diag([.25,4]);X=np.diag([1/16,16])
c(f,'hard',2,'ordinary product and composite gain',[norm(W0)*norm(W1),norm(W1@W0)],[16,1])
c(f,'hard',2,'weighted first layer',W0.T@X@W0,np.eye(2))
c(f,'hard',2,'weighted last layer',W1.T@W1,X)
K=np.array([[0,-.2],[.2,0]]);S=np.eye(2)+K+K@K/2
c(f,'hard',3,'truncated squared Gram',S.T@S,np.eye(2)*1.0004)
c(f,'hard',3,'norm and ten-layer bounds',[norm(S),(1+.2**3/6)**10,norm(S)**10],[1.000199980003999,1.0134136184425453,1.002001600640127])
c(f,'hard',4,'contraction threshold',math.ceil(math.log(.1/3)/math.log(.8)),16)
c(f,'hard',4,'adjacent contraction values',[3*.8**15,3*.8**16],[.105553116266496,.0844424930131969])
c(f,'hard',4,'nonzero initial storage',[4+4*9,math.sqrt(40)],[40,6.32455532033676])
f='nn-in-the-loop.html'
c(f,'easy',1,'equilibrium and closed-loop multiplier',[1/(1-.75),.25*4+1,.5+.25],[4,2,.75])
c(f,'easy',2,'Lyapunov coefficient and sample',[2*(.8**2-1),2*2**2,2*(.8*2)**2],[-.72,8,5.12])
P=np.diag([4,1]);a=np.array([2,1]);x=np.linalg.inv(P)@a/np.sqrt(2)
c(f,'easy',3,'containment squared radius',a@np.linalg.inv(P)@a,2)
c(f,'easy',3,'attaining point energy and output',[x@P@x,a@x],[1,np.sqrt(2)])
c(f,'easy',4,'shifted activation examples',[relu(1)-1,relu(-1),relu(1.5)-1,relu(-.5)],[0,0,.5,0])
t=math.tanh(1)
c(f,'medium',1,'tanh sector slope and QC',[t,1-t*t,2*t*(1-t)],[.7615941559557649,.41997434161402614,.363136995139582])
c(f,'medium',2,'affine box centre radius endpoints',[2*1-3*(-1)+1,2*.2+3*.5,2*.8-3*(-.5)+1,2*1.2-3*(-1.5)+1],[6,1.9,4.1,7.9])
c(f,'medium',3,'sector threshold and stable endpoints',[(1.2-1)/.5,1.2-.5,1.2-.5*.5],[.4,.7,.95])
a=np.array([1,.5]);prev=np.array([0,1]);terms=a*(a-prev)
c(f,'medium',4,'IQC terms and partial sums',list(terms)+list(np.cumsum(terms)),[1,-.25,1,.75])
c(f,'medium',4,'IQC sum-of-squares identity',np.sum(terms),.5*a[-1]**2+.5*np.sum((a-prev)**2))
c(f,'hard',1,'local contraction and exterior divergence',[(.8/2)**2,1.1*2],[.16,2.2])
M=np.array([[-.56,.9],[.9,-1.75]])
c(f,'hard',2,'stability determinant',np.linalg.det(M),.17)
c(f,'hard',2,'stability quadratic expansion',M,np.outer([1.2,-.5],[1.2,-.5])-np.diag([1,0])+np.array([[-1,1.5],[1.5,-2]]))
c(f,'hard',2,'negative eigenvalues',np.linalg.eigvalsh(M),[-2.233899903605334,-.076100096394666],tol=1e-7)
for t in [0,1,5,20]:
 direct=.25
 for _ in range(t):direct=.5*direct+.02
 c(f,'hard',3,f'disturbed recursion at {t}',direct,.5**t*.25+.04*(1-.5**t))
c(f,'hard',3,'invariance next bound and limiting radius',[.5*.25+.02,math.sqrt(.04)],[.145,.2])
c(f,'hard',4,'shifted functions differ at negative increment',[relu(-.5),relu(-.5+1)-1],[0,-.5])
f='verification.html'
c(f,'easy',1,'counterexample logits and maximum',[2*0+1,-0+2,1-3*0],[1,2,1])
c(f,'easy',2,'affine interval endpoints',[2*1-3*1+1,2*2-3*(-1)+1],[0,8])
c(f,'easy',3,'ReLU line checks',[.4*(-1),.6*(-1+2),.4*1,.6*(1+2)],[-.4,.6,.4,1.8])
c(f,'easy',4,'conformal rank and interval',[math.ceil(10*.8),2-.8,2+.8],[8,1.2,2.8])
c(f,'medium',1,'correlated cancellation',[relu(x)-relu(x) for x in [-1,0,1]],[0,0,0])
c(f,'medium',2,'wrong-side counterexample and correct min',[1-2*relu(-.5),1-2*(2/3)*(-.5+1),1-2*relu(2)],[1,1/3,-3])
from statistics import NormalDist
c(f,'medium',3,'normal quantile radius and norm conversion',[.5*NormalDist().inv_cdf(NormalDist().cdf(2)),1/math.sqrt(100)],[1,.1])
c(f,'medium',4,'Hoeffding integer count and lower success',[math.ceil(math.log(100)/(.02)),.98-.1,.95+.1],[231,.88,1.05])
a=np.array([3,-4]);x0=np.array([1,2]);base=a@x0+2
c(f,'hard',1,'two norm-ball ranges',[base-.2*norm(a),base+.2*norm(a),base-.2*np.sum(np.abs(a)),base+.2*np.sum(np.abs(a))],[-4,-2,-4.4,-1.6])
c(f,'hard',1,'attaining Euclidean and box points',[a@(x0-.2*a/norm(a))+2,a@(x0-.2*np.sign(a))+2],[-4,-4.4])
c(f,'hard',2,'trajectory ranks and joint budget',[.1/4,math.ceil(40*.975),math.ceil(20*.975),1-4*.1,.9**4],[.025,39,20,.6,.6561])
def tail(n):return sum(math.comb(n,i)*.1**i*.9**(n-i) for i in range(3))
c(f,'hard',3,'explicit scenario count',math.ceil(20*(math.log(20)+3)),120)
c(f,'hard',3,'exact scenario tails',[tail(60),tail(61)],[.05304508181599274,.04911828153099453])
c(f,'hard',3,'minimal exact count',next(n for n in range(3,121) if tail(n)<=.05),61)
c(f,'hard',4,'feasibility conditioning',[.04/.5,.5+.04,1-(.5+.04)],[.08,.54,.46])
# Ensure every exercise is represented, including conceptual ones with diagnostic numeric examples.
coverage=json.loads(Path('reports/learning-review/modules-certified-coverage.json').read_text())
expected={(p,e['id']) for p,meta in coverage.items() for e in meta['exercises']}
seen={(c['page'],c['exercise']) for c in checks}
assert expected==seen,(expected-seen,seen-expected)
report=dict(passed=True,checks=len(checks),exercises_covered=len(seen),results=checks,limitations='Arithmetic, matrix identities and diagnostic examples; does not replace proof/assumption review or validated numerical certification.')
Path('reports/learning-review/modules-certified-math.json').write_text(json.dumps(report,indent=2))
print(json.dumps(dict(passed=True,checks=len(checks),exercises_covered=len(seen))))
