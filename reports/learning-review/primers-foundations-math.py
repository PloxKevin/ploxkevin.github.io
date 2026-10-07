"""Independent arithmetic checks for new foundations practice and first-course examples.
Run from repository root: python reports/learning-review/primers-foundations-math.py
Proof validity and teaching coverage also require the documented manual review.
"""
import json, math
from pathlib import Path
import numpy as np
checks=[]
def check(ex, description, actual, expected, atol=1e-10):
    actual=np.asarray(actual,dtype=float); expected=np.asarray(expected,dtype=float)
    assert np.allclose(actual,expected,rtol=0,atol=atol),(ex,description,actual,expected)
    checks.append({'exercise':ex,'check':description,'actual':actual.tolist(),'passed':True})
def v(x): return np.array(x,dtype=float)
def norm(x): return float(np.linalg.norm(x))
# Primer 0: explicit calculations, endpoints, tail/index thresholds and game orders.
check('mb-ex-sequences-1','first four terms',[3/(t+1) for t in range(4)],[3,1.5,1,.75])
check('mb-ex-sequences-1','smallest strict-tolerance index',next(t for t in range(100) if 3/(t+1)<.1),30)
check('mb-ex-sequences-2','four terms and tail',[sum(2*.5**t for t in range(4)),sum(2*.5**t for t in range(4,100))],[3.75,.25])
check('mb-ex-sequences-2','smallest return-tail budget',next(t for t in range(100) if 2*.5**t/(1-.5)<=.01),9)
check('mb-ex-sequences-3','telescoping budget and excursion count',[3/.5,(3/.5)/(.2**2)],[6,150])
check('mb-ex-bounds-1','first sequence values',[1-1/n for n in range(1,5)],[0,.5,2/3,.75])
check('mb-ex-bounds-2','initial maximum and two subsequential limits',[(-1)**0+1,(-1)**100000+1/100001,(-1)**100001+1/100002],[2,1,-1],atol=1e-5)
phi=v([[0,2],[1,0]])
check('mb-ex-bounds-3','two orders',[phi.max(axis=1).min(),phi.min(axis=0).max()],[1,0])
check('mb-ex-topology-1','missing-endpoint sequence',-1+1/100000,-1,atol=1e-5)
check('mb-ex-topology-2','approaching unattained infimum',(1/10000)**2,0,atol=1e-8)
check('mb-ex-topology-3','fine/coarse margin',[.35-3*.1,.35-3*.2],[.05,-.25])
for n in [1,2,10,100]:
    assert 2*n*n<=2*n*n+3*n+1<=6*n*n
check('mb-ex-asymptotics-1','growth ratio limit sample',(2*10**12+3*10**6+1)/10**12,2,atol=4e-6)
check('mb-ex-asymptotics-2','budgets',[math.ceil((4/.1)**2),math.ceil(8/.1),1600*100,80*1000],[1600,80,160000,80000])
check('mb-ex-asymptotics-3','finite regret bound',5*math.log(1e4)/math.sqrt(1e4),.4605170185988092)
# Primer A: independent matrix multiplication, numpy eigen/singular decompositions and solves.
x=v([2,-1,2]); y=v([1,2,0])
check('la-ex-norms-1','dot product and vector norms',[x@y,np.abs(x).sum(),norm(x),np.max(np.abs(x))],[0,5,3,2])
w=v([3,-4]); check('la-ex-norms-2','attaining perturbations',[w@v([.2,-.2]),w@v([.12,-.16]),norm([.12,-.16])],[1.4,1,.2])
check('la-ex-norms-3','unit-disc distance',norm(v([3,4])-v([.6,.8])),4)
A=v([[1,-2],[0,3]])
check('la-ex-matrix-norms-1','three matrix norms',[np.linalg.norm(A,1),np.linalg.norm(A,np.inf),np.linalg.norm(A,'fro')],[5,3,math.sqrt(14)])
A=np.diag([3,.5]); B=np.diag([.5,3])
check('la-ex-matrix-norms-2','composition and bound',[np.linalg.norm(A@B,2),np.linalg.norm(A,2)*np.linalg.norm(B,2)],[1.5,9])
A=np.diag([.5,.25]); inv=np.linalg.inv(np.eye(2)-A)
check('la-ex-matrix-norms-3','inverse',inv,np.diag([2,4/3]))
for t in [7,8]:
    partial=sum((np.linalg.matrix_power(A,k) for k in range(t)),np.zeros((2,2)))
    check('la-ex-matrix-norms-3',f'tail with {t} terms',np.linalg.norm(inv-partial,2),2**(1-t))
A=v([[3,1],[1,3]]); q=v([[1,1],[1,-1]])/math.sqrt(2)
check('la-ex-spectral-1','eigenvalues',np.linalg.eigvalsh(A),[2,4])
check('la-ex-spectral-1','orthonormal directions',q.T@q,np.eye(2))
x=v([1,2]); check('la-ex-spectral-2','quadratic form and quotient',[x@A@x,x@A@x/(x@x)],[19,3.8])
N=v([[1,4],[0,1]]); x=v([1,-1]); S=(N+N.T)/2
check('la-ex-spectral-3','nonsymmetric counterexample',[x@N@x,*np.linalg.eigvalsh(S)],[-2,-1,3])
check('la-ex-psd-1','classification eigenvalues',[*np.linalg.eigvalsh(np.diag([2,0])),*np.linalg.eigvalsh(v([[2,3],[3,2]]))],[0,2,-1,5])
P=v([[4,2],[2,2]]); L=np.linalg.cholesky(P); b=v([6,4])
check('la-ex-psd-2','Cholesky factor',L,[[2,0],[1,1]])
check('la-ex-psd-2','solve',np.linalg.solve(P,b),[1,1])
check('la-ex-psd-2','log determinant',np.linalg.slogdet(P)[1],math.log(4))
P=np.diag([4,1]); g=v([1,2]); xs=v([1/(2*math.sqrt(17)),4/math.sqrt(17)])
check('la-ex-psd-3','ellipsoid attaining support',[xs@P@xs,g@xs,math.sqrt(g@np.linalg.solve(P,g))],[1,math.sqrt(17)/2,math.sqrt(17)/2])
A=np.diag([2,-1]); s=np.linalg.svd(A,compute_uv=False)
check('la-ex-svd-1','singular values and conditioning',[*s,np.linalg.norm(A,'fro'),np.linalg.cond(A)],[2,1,math.sqrt(5),2])
A=v([[1,2]]); x=(np.linalg.pinv(A)@v([5])); check('la-ex-svd-2','minimum-norm solution',x,[1,2])
check('la-ex-svd-2','orthogonal null direction',x@v([-2,1]),0)
A=np.diag([3,1]); x0=v([1,1])/math.sqrt(2); x1=A.T@A@x0; x1/=norm(x1)
check('la-ex-svd-3','power estimates',[norm(A@x0),norm(A@x1),np.linalg.norm(A/norm(A@x0),2)],[math.sqrt(5),math.sqrt(730/82),3/math.sqrt(5)])
M=v([[2,1,0],[1,3,0],[0,0,4]])
check('la-ex-blocks-1','block product',M@v([1,2,3]),[4,7,12])
check('la-ex-blocks-1','trace and determinant',[np.trace(M),np.linalg.det(M)],[9,20])
M=v([[4/3,2],[2,3]]); check('la-ex-blocks-2','boundary null direction',M@v([3,-2]),[0,0])
V=np.diag([2,1]); u=v([1,2]); M=V+np.outer(u,u)
check('la-ex-blocks-3','rank-one determinant and inverse',[np.linalg.det(M),np.linalg.slogdet(M)[1]-np.linalg.slogdet(V)[1]],[11,math.log(5.5)])
check('la-ex-blocks-3','inverse',np.linalg.inv(M),v([[5,-2],[-2,3]])/11)
Q=np.diag([1,-1]); check('la-ex-structured-1','reflection',[*Q@v([3,4]),norm(Q@v([3,4])),np.linalg.det(Q)],[3,-4,5,-1])
P=np.diag([1,0]); check('la-ex-structured-2','projection residual',v([3,4])-P@v([3,4]),[0,4])
check('la-ex-structured-2','idempotence',P@P,P)
A=v([[0,-1],[1,0]]); Q=(np.eye(2)-A)@np.linalg.inv(np.eye(2)+A)
check('la-ex-structured-3','Cayley product',Q,[[0,1],[-1,0]])
check('la-ex-structured-3','orthogonality',Q.T@Q,np.eye(2))
# Exact polynomial integrals by coefficient antiderivatives (independent from worked text).
def polyint(coeff): return sum(c/(k+1) for k,c in enumerate(coeff))
check('la-ex-functions-1','function inner products and residual norm',[polyint([0,1]),polyint([1]),polyint([0,0,1]),polyint([.25,-1,1])],[.5,1,1/3,1/12])
Phi=v([[1,0],[1,1]]); K=Phi@Phi.T
check('la-ex-functions-2','feature Gram matrix',K,[[1,1],[1,2]])
for a in [v([1,-1]),v([2,3]),v([0,0])]:
    check('la-ex-functions-2','Gram sum-of-squares identity',a@K@a,norm(Phi.T@a)**2)
y=v([1,3]); alpha=np.linalg.solve(K,y)
check('la-ex-functions-3','RKHS interpolant and norm',[*alpha,y@alpha,*Phi.T@alpha],[-1,2,5,1,2])
# Primer B: analytic derivatives are checked against central finite differences where useful.
def derivative(f,x,h=1e-5): return (f(x+h)-f(x-h))/(2*h)
def gradient(f,x,h=1e-5):
    return v([derivative(lambda t:f(x+np.eye(len(x))[i]*(t-x[i])),x[i],h) for i in range(len(x))])
f=lambda x:x[0]**2+x[0]*x[1]+2*x[1]**2
check('opt-ex-derivatives-1','gradient finite difference',gradient(f,v([1,-1])),[1,-3],atol=1e-8)
check('opt-ex-derivatives-2','curve derivative',derivative(lambda t:1-t*t-t**4,1),-6,atol=1e-8)
actual=math.exp(.1)+.2**2; approx=1+.1+.1**2/2+.2**2; bound=math.exp(.1)*.1**3/6
assert 0<=actual-approx<=bound
check('opt-ex-derivatives-3','Taylor model',approx,1.145)
check('opt-ex-derivatives-3','Taylor error',actual-approx,.0001709180756477)
A=np.diag([1,2]); b=v([1,1]); f=lambda x:norm(A@x-b)**2
check('opt-ex-matrix-calculus-1','least-squares gradient',gradient(f,v([0,0])),[-2,-4],atol=1e-8)
check('opt-ex-matrix-calculus-1','least-squares solve',np.linalg.solve(A,b),[1,.5])
X=np.diag([2,3]); E=v([[1,1],[1,0]])
check('opt-ex-matrix-calculus-2','log-det finite difference',derivative(lambda t:np.linalg.slogdet(X+t*E)[1],0),.5,atol=1e-8)
check('opt-ex-matrix-calculus-2','inverse finite difference',derivative(lambda t:np.linalg.inv(X+t*E),0),-v([[.25,1/6],[1/6,0]]),atol=1e-8)
# Expected values below are separately derived from a direct solve, not the sensitivity formula.
solve=lambda t:np.linalg.solve(np.diag([1+t,2]),v([2,4]))
check('opt-ex-matrix-calculus-3','solution derivative',derivative(solve,0),[-2,0],atol=1e-8)
check('opt-ex-matrix-calculus-3','first-order prediction error',norm(solve(.01)-v([1.98,2])),.0001980198019802)
check('opt-ex-lipschitz-1','function chord near endpoint',(2**2-(2-1e-6)**2)/1e-6,4,atol=2e-6)
check('opt-ex-lipschitz-2','dimension-dependent margins',[.15-2*.1/2,.15-2*math.sqrt(3)*.1/2,.15/math.sqrt(3),13**3],[.05,-.023205080756887736,.08660254037844387,2197])
d=0; ds=[]
for t in range(6): d=1.2*d+.01; ds.append(d)
check('opt-ex-lipschitz-3','unrolled recurrence',[ds[4],ds[5],.2-2*ds[4],.2-2*ds[5]],[.074416,.0992992,.051168,.0014016])
a=v([-1,1]); check('opt-ex-convexity-1','failed midpoint',np.mean(a),0)
for a in [-3,-2,0,2,3]:
    check('opt-ex-convexity-2',f'Hessian spectrum at a={a}',np.linalg.eigvalsh(v([[2,a],[a,2]])),sorted([2+a,2-a]))
for y in [-2,-1,0,1,2]:
    x=max(0,y); check('opt-ex-convexity-3',f'conjugate at y={y}',y*x-x*x/2,max(y,0)**2/2)
check('opt-ex-descent-1','gradient iterates',[2*(1-4*.4),2*(1-4*.4)**2,2*(1-4*.6),2*(1-4*.6)**2],[-1.2,.72,-2.8,3.92])
H=np.diag([2,8]); c=v([2,8]); x=v([3,0]); g=H@x-c
check('opt-ex-descent-2','Newton step',x+np.linalg.solve(H,-g),[1,1])
check('opt-ex-descent-2','gradient step',x-g/8,[2.5,1])
x=4; g=1-1/x; delta=-g/(1/x**2); f=lambda z:z-math.log(z)
check('opt-ex-descent-3','Newton direction and first domain candidate',[delta,x+delta/4],[-12,1])
assert x+delta<=0 and x+delta/2<=0 and f(x+delta/4)<=f(x)+.25*.25*g*delta
check('opt-ex-constraints-1','active multiplier',-2*(1-3),4)
x=v([.5,.5]); check('opt-ex-constraints-2','KKT stationarity',x-v([2,2])+1.5*v([1,1]),[0,0])
check('opt-ex-constraints-2','optimal objective',.5*norm(x-v([2,2]))**2,9/4)
check('opt-ex-constraints-3','penalty minimiser/objective',[10/8,(10/8-2)**2+3*(10/8-1)**2],[1.25,.75])
check('opt-ex-constraints-3','KKT residuals',[abs(2*(.9-2)+2.2),2.2*(1-.9)],[0,.22])
Q=np.diag([2,4]); c=v([-2,4]); xs=np.linalg.solve(Q,-c)
check('opt-ex-programs-1','QP solution and omitted-constant value',[*xs,.5*xs@Q@xs+c@xs],[1,-1,-3])
verts=v([[0,0],[2,0],[2,1],[0,3]])
check('opt-ex-programs-2','vertex objectives',verts@v([2,1]),[0,4,5,3])
a=v([1,2]); check('opt-ex-programs-3','half-space projection',4*a/(a@a),[.8,1.6])
xs=v([1,1.5]); check('opt-ex-programs-3','full QP stationarity',xs-v([1,2])+.5*v([0,1]),[0,0])
check('opt-ex-programs-3','cost and maximum box margin',[.5*xs@xs,1.5+2*1.5],[1.625,4.5])
check('opt-ex-minmax-1','approximation gap',1-.99,.01)
margins=v([[.6,.1],[.35,.3],[.8,-.05]])
check('opt-ex-minmax-2','worst margins',margins.min(axis=1),[.1,.3,-.05])
x=np.linspace(0,2,101); y=np.linspace(-3,0,301); L=(x[:,None]-1)**2-(y[None,:]+2)**2
check('opt-ex-minmax-3','both saddle values',[L.max(axis=1).min(),L.min(axis=0).max()],[0,0])
# Baseline mini-examples (not graded exercise IDs).
A=v([[1,2],[0,1]]); B=v([[2,0],[1,3]])
check('la-first-course','two product orders',v([A@B,B@A]),v([[[4,6],[1,3]],[[2,4],[1,5]]]))
check('la-first-course','linear solve',np.linalg.solve(A,v([4,1])),[2,1])
check('opt-first-course','chain-rule example',derivative(lambda t:(2*t+1)**2,1),12,atol=1e-8)
covered={c['exercise'] for c in checks if '-ex-' in c['exercise']}
assert len(covered)==60,len(covered)
report={'checked_new_exercises':len(covered),'arithmetic_checks':len(checks),'passed':True,'scope':'Independent numerical recomputation of every new exercise; manual proof/teaching review is also recorded in primers-foundations-review.json.','checks':checks}
Path('reports/learning-review/primers-foundations-math.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))
