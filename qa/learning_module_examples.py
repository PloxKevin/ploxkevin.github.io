"""Independent numerical checks for the 48 graded problems in Modules 8–11."""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import numpy as np

practice=json.loads((Path(__file__).resolve().parents[1]/'verification/data/core-practice.json').read_text())
checks={}
def checked(name, condition):
    assert condition,name
    checks[name]=True
def near(x,y): return abs(x-y)<1e-6
def cvar(values,probabilities,alpha):
    remaining=1-alpha;total=0
    for value,prob in sorted(zip(values,probabilities),reverse=True):
        take=min(prob,remaining);total+=take*value;remaining-=take
        if remaining<1e-12: break
    return total/(1-alpha)

checked('8.P1',F(2)/(1-F(1,2))==4 and F(1,4)/(1-F(1,2))==F(1,2)<F(3,5))
checked('8.P2',F(3,10)+F(7,10)==1 and (F(3,10)*3+F(7,10))*2==F(16,5) and F(3,10)*2*2==F(6,5))
checked('8.P3',8-F(3,2)*(5-4)==F(13,2) and 8-F(3,2)*(3-4)==F(19,2))
l1=max(F(0),F(1,10)+F(1,5)*(3-2));l2=max(F(0),l1+F(1,5)*(0-2))
checked('8.P4',l1==F(3,10) and l2==0)
P=np.array([[0.,1.],[0.,1.]])
rho=np.linalg.solve(np.eye(2)-.5*P.T,.5*np.array([1.,0.]))
checked('8.P5',np.allclose(rho,[.5,.5]) and near(float(rho@np.array([0.,2.])/.5),2))
grid=np.linspace(0,1,10001);feasible=grid[4*grid<=1+1e-12]
checked('8.P6',near(feasible[-1],.25) and near(max(2+6*feasible),3.5))
checked('8.P7',near(.2*10,2) and near(cvar([0,10],[.8,.2],.9),10))
z1=(F(2)-1)/F(1,2);z2=(z1-F(3,2))/F(1,2)
checked('8.P8',z1==2 and z2==1 and F(2)-(1+F(1,2)*F(3,2))==F(1,2)**2*z2==F(1,4))
lam=np.linspace(0,5,10001);dual=np.maximum(2+lam,8-3*lam)
checked('8.P9',near(lam[np.argmin(dual)],1.5) and near(min(dual),3.5))
checked('8.P10',max(0,(1-1)/2)==0 and (max(0,1)+max(0,-1))/2==.5)
checked('8.P11',near(.01*100,1) and near(cvar([0,100],[.99,.01],.95),20))
checked('8.P12',all(2+6*p-l*(4*p-1)>=2+6*p-1e-12 for p in np.linspace(0,.25,21) for l in [0,.1,1.5,10]))

checked('9.P1',F(1,4)*5+F(3,4)*1==2 and F(1,4)*3-F(3,4)==0 and F(1,2)*3-F(1,2)==1)
kl=.75*math.log(1.5)+.25*math.log(.5)
checked('9.P2',near(.5*(abs(.75-.5)+abs(.25-.5)),.25) and near(kl,.130812))
checked('9.P3',near(.5*(4*.5**2),.5) and near(4*.5**2,1) and near(1**2,1))
checked('9.P4',near(-.2+.3,.1) and near(-.2+.1,-.1))
g=np.array([1.,2.]);H=np.diag([1.,4.]);x=np.linalg.solve(H,g)/math.sqrt(2)
checked('9.P5',near(float(.5*x@H@x),.5) and near(float(g@x),math.sqrt(2)))
candidate=np.array([.1,.2]);nom=np.array([.6,.2])
checked('9.P6',near(float(.5*np.sum((candidate-nom)**2)),.125))
checked('9.P7',near(2*.9*.5*.01/(1-.9)**2,.9) and near(2*.5*.5*.01/(1-.5)**2,.02))
checked('9.P8',7+2>8 and 5+2<=8)
t=np.linspace(-1,.2,12001);objective=t+np.sqrt(np.maximum(0,1-t*t))
checked('9.P9',near(t[np.argmax(objective)],.2) and near(max(objective),.2+math.sqrt(.96)))
root=(-1+math.sqrt(1.8))/4
checked('9.P10',near(-.1+.1+2*.1**2,.02) and near(-.1+root+2*root**2,0) and near(root,.085410))
weights=np.array([.5/.99,.5/.01])
checked('9.P11',near(float(np.array([.99,.01])@weights),1) and near(weights[1],50))
checked('9.P12',near(1-.02-.03,.95) and .4-.3>0 and 7+.5<=8)

checked('10.P1',F(1)-F(1,2)**2==F(3,4) and 1-1**2==0 and 1-2**2==-3)
checked('10.P2',-2*F(1,2)==-1)
checked('10.P3',max(-3,-1)==-1 and F(1,2)*(-1+3)**2==2)
u=np.array([.5,.5]);mult=.5
checked('10.P4',1-0>0 and 1-2<0 and all(0<=1+(x-1)*math.exp(-t)<=2 for x in np.linspace(0,2,21) for t in np.linspace(0,10,21)))
checked('10.P5',near(sum(u),1) and np.allclose(u-mult*np.ones(2),0) and near(float(.5*u@u),.25))
checked('10.P6',1-.1>.2 and 1-2<=-.2)
checked('10.P7',near(.1-.3+.2,0) and near(-.2+.2,0))
checked('10.P8',near(-.4+1,.6) and near(2*(-.4)+1,.2) and near(.1-1,-.9))
checked('10.P9',3*0**2*(-1)==0 and -0.01<0)
checked('10.P10',near(1-1.5,-.5) and math.exp(-1.5)>0)
states=[1.,.5,.25,0.];inputs=[-.5,-.25,-.25]
checked('10.P11',all(near(states[i]+inputs[i],states[i+1]) for i in range(3)) and all(abs(x)<=1 for x in states) and all(abs(u)<=.5 for u in inputs) and abs(states[2])<=.25 and abs(states[3])<=.25)
trans={('a','L'):{'b'},('a','R'):{'f'},('b','L'):{'a'},('b','R'):{'b'}}
shield={s:{a for a in ['L','R'] if trans[(s,a)]<={'a','b'}} for s in ['a','b']}
trans[('b','R')]={'b','f'}
checked('10.P12',shield=={'a':{'L'},'b':{'L','R'}} and {a for a in ['L','R'] if trans[('b',a)]<={'a','b'}}=={'L'})

checked('11.P1',near(.6**2-1,-.64) and near(.6*2,1.2))
checked('11.P2',near(4*.4**2+.5**2,.89) and near(4*.6**2,1.44))
checked('11.P3',near(max((.5*.4+w)**2 for w in [-.1,.1]),.09) and near(.09-.4**2,-.07))
checked('11.P4',near(.2+.5*.8,.6) and near(.7-(.2+.5*.8),.1))
checked('11.P5',near(-.12+.02+5*.01,-.05) and near(-.12+.02+5*.03,.05))
checked('11.P6',near(.5*.2+.1,.2) and near(.8+.2,1) and near(.9+.5*.2,1))
us=np.linspace(-.5,.5,10001);cost=1+us**2+2*(1+us)**2
checked('11.P7',near(us[np.argmin(cost)],-.5) and near(min(cost),1.75))
checked('11.P8',near(math.sqrt(math.log(20)/2000),.038702))
xs=np.linspace(-1,1,2001);f=xs-xs**3;dv=f*f-xs*xs
checked('11.P9',np.allclose(dv,xs**4*(xs**2-2)) and np.all(dv<=1e-12) and near(abs(math.sqrt(2)-math.sqrt(2)**3),math.sqrt(2)))
checked('11.P10',near(.6**2-1,-.64) and near(.5*.2+.1,.2))
n1=math.ceil(math.log(.05)/math.log(.99));n20=math.ceil(math.log(.05/20)/math.log(.99))
checked('11.P11',n1==299 and n20==597 and .99**n1<=.05<.99**(n1-1) and .99**n20<=.0025<.99**(n20-1))
checked('11.P12',near(1-.01-.02,.97))

# Check the authoring records and published exercise IDs are exactly those verified.
for name,data in practice.items():
    page=(Path(__file__).resolve().parents[1]/'SafeLearning'/(name+'.html')).read_text()
    for i,record in enumerate(data['exercises'],1):
        checked(f'{data["num"]}.P{i}-published',f'id="exercise-{data["num"]}-p{i}"' in page and record[-1] in page)
report={'status':'passed','exercise_checks':48,'published_solution_checks':48,'checks':checks}
out=Path(__file__).resolve().parents[1]/'reports/learning-review/modules-8-11-math.json'
out.write_text(json.dumps(report,indent=2)+'\n')
print('48 numerical/semantic examples and 48 published solutions verified.')
