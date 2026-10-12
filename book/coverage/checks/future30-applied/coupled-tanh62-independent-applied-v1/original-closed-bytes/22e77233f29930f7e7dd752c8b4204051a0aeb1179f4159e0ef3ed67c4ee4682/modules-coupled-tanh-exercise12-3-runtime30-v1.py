from pathlib import Path
from fractions import Fraction as Q
import json, math, hashlib
HERE=Path(__file__);OUT=Path('/tmp/modules-coupled-tanh-exercise12-3-runtime30-result-v1.json');assert not OUT.exists()
# This is an actual numeric grid/Newton run, not a substitute for the Lean
# global-optimum and rational enclosure proofs in the coherent TMP source.
def f(x):return math.tanh(x+1)-math.tanh(x-1)-.5
def direct_network(x):return -math.tanh(-x-1)+math.tanh(-x+1)-.5
def df(x):return (1-math.tanh(x+1)**2)-(1-math.tanh(x-1)**2)
def d2f(x):
 p,m=math.tanh(x+1),math.tanh(x-1)
 return -2*(1-p*p)*p+2*(1-m*m)*m
def d3f(x):
 p,m=math.tanh(x+1),math.tanh(x-1)
 return -2*(1-p*p)*(1-3*p*p)+2*(1-m*m)*(1-3*m*m)
points=[i/1000 for i in range(6001)];best=max(points,key=lambda x:abs(df(x)))
x=best;newton=[]
for i in range(12):
 old=x;residual=d2f(old);den=d3f(old);assert abs(den)>.01
 x=old-residual/den;newton.append({'iteration':i,'input_before':old,'second_derivative_residual':residual,'third_derivative':den,'input_after':x})
 if abs(x-old)<1e-14:break
r=math.tanh(1);k=r*r;u=(-3*(1-k)+math.sqrt(9*(1-k)**2+4*k))/(2*k);s=math.sqrt(u);analytic_x=math.atanh(s)
L=4*r*(1-k)*s*(1-u)/(1-k*u)**2
assert math.isclose(x,analytic_x,rel_tol=0,abs_tol=2e-13)
assert 1.0605<x<1.0615 and .93349<L<.933495 and abs(d2f(x))<2e-14
assert math.isclose(abs(df(x)),L,rel_tol=0,abs_tol=2e-14)
for t in [-6,-2,-1.0610852744162456,0,1.0610852744162456,2,6]:
 assert math.isclose(f(t),direct_network(t),rel_tol=0,abs_tol=1e-14)
 assert math.isclose(f(-t),f(t),rel_tol=0,abs_tol=1e-14)
 assert math.isclose(df(-t),-df(t),rel_tol=0,abs_tol=1e-14)
# Exact Fraction interval computations use the same literal enclosures as Lean.
rlo,rhi=Q('.7615941559'),Q('.7615941561');klo,khi=Q('.5800256582'),Q('.5800256587');ulo,uhi=Q('.617919996'),Q('.617919998');slo,shi=Q('.786078873'),Q('.786078876')
P=lambda k,u:1-3*(1-k)*u-k*u*u
assert rlo*rlo>klo and rhi*rhi<khi
assert min(P(klo,ulo),P(khi,ulo))>0 and max(P(klo,uhi),P(khi,uhi))<0
assert slo*slo<ulo and shi*shi>uhi
Nlo=4*rlo*(1-khi)*slo*(1-uhi);Nhi=4*rhi*(1-klo)*shi*(1-ulo)
Dlo=(1-khi*uhi)**2;Dhi=(1-klo*ulo)**2;Llo,Lhi=Nlo/Dhi,Nhi/Dlo
assert Q('.93349')<Llo<Lhi<Q('.933495') and Q('.07')<1/Lhi-1<1/Llo-1<Q('.075')
result={'status':'passed_actual_grid_newton_and_exact_fraction_support_computations','runtime_helper_sha256':hashlib.sha256(HERE.read_bytes()).hexdigest(),'network_weights':{'W0':[[-1],[-1]],'W1':[[-1,1]],'b0':[-1,1],'b1':[-.5]},'grid':{'lo':0,'hi':6,'step':.001,'sample_count':len(points),'maximizing_grid_point':best,'grid_max_derivative_magnitude':abs(df(best))},'newton_on_actual_printed_second_derivative':newton,'newton_result':x,'newton_residual':d2f(x),'analytic_critical_root':u,'analytic_attaining_slope':s,'analytic_attaining_input':analytic_x,'analytic_exact_gain_evaluation':L,'relative_one_bound_looseness':1/L-1,'printed_point_sech_squared_terms':[1/math.cosh(-.061)**2,1/math.cosh(-2.061)**2],'exact_fraction_gain_enclosure':{'lower':str(Llo),'upper':str(Lhi)},'rigorous_global_maximum_claimed_by_runtime':False,'lean_draft_compiled':False,'coverage_complete':False}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'result':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'grid_point':best,'newton_point':x,'gain':L,'status':result['status']}))
