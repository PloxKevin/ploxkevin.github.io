"""Prepare barrier-page Source90 decisions without changing teaching pages."""
from pathlib import Path
from hashlib import sha256
import json

BASE=Path('book/solutions/baseline-source90/pages/barriers.html.json')
DEST=Path('book/solutions/drafts/barriers-thorough-solutions-v1.json')
replacement={}
rationale={}

def replace(a,why,body):
    replacement[a]=body.strip()+'\n'
    rationale[a]=why

replace('exercise-18', 'Derive the barrier chain and characteristic polynomial, distinguish the two initial-state tests from the input-containing final inequality, and prove invariance for the selected gains by two integrating factors.', r'''
<p>The barrier is $h=1-p$. Differentiate using the two state equations: $\dot h=-\dot p=-v$ and $\ddot h=-\dot v=-u$. The input first appears in the second derivative, so the relative degree is $2$.</p>
<div class="math-block">$$\eta_b=\begin{bmatrix}1-p\\-v\end{bmatrix},\quad F=\begin{bmatrix}0&1\\0&0\end{bmatrix},\quad G=\begin{bmatrix}0\\1\end{bmatrix}.$$</div>
<p>With the virtual input $\mu=\ddot h=-u$, the chain equation $\dot\eta_b=F\eta_b+G\mu$ has first row $\dot h=-v$ and second row $\frac{d}{dt}(-v)=-u$. For $K_\alpha=[\kappa_1\ \kappa_2]$, the ECBF constraint is</p>
<div class="math-block">$$-u\ge-\kappa_1(1-p)+\kappa_2v,\qquad u\le\kappa_1(1-p)-\kappa_2v.$$</div>
<p>The virtual closed-loop matrix is $F-GK_\alpha=\begin{bmatrix}0&1\\-\kappa_1&-\kappa_2\end{bmatrix}$. Its characteristic polynomial is $\lambda^2+\kappa_2\lambda+\kappa_1$. Choose real negative poles $-p_1,-p_2$ with positive magnitudes $p_1,p_2$. Matching $(\lambda+p_1)(\lambda+p_2)$ gives $\kappa_1=p_1p_2$ and $\kappa_2=p_1+p_2$, in particular $\kappa_2^2\ge4\kappa_1$.</p>
<p>For the nested construction, $\nu_0=h$ and $\nu_1=\dot h+p_1h=-v+p_1(1-p)$. The initial-state requirements are $\nu_0(x_0)\ge0$ and $\nu_1(x_0)\ge0$. At $(p_0,v_0)=(0,1)$, these become $1\ge0$ and $-1+p_1\ge0$, so $p_1\ge1$. These use the positive pole magnitudes: using the negative eigenvalue in $p_1\ge-\dot h(0)/h(0)$ would reverse its intended meaning. If $h(0)=0$, division is unavailable and the test is instead $\dot h(0)\ge0$.</p>
<p>The final nested expression is</p>
<div class="math-block">$$\nu_2=\dot\nu_1+p_2\nu_1=-u-(p_1+p_2)v+p_1p_2(1-p).$$</div>
<p>It contains the input, so $\nu_2\ge0$ is the condition to enforce at every time, including the initial instant. It is not an additional condition on the initial state alone. An admissible choice is $p_1=p_2=2$, giving $K_\alpha=[4\ \ 4]$ and</p>
<div class="math-block">$$u\le4(1-p)-4v.$$</div>
<p>Initially the right side is zero, and the auxiliary initial value is $\nu_1(0)=-1+2=1$. With unrestricted input, the constraint is feasible; for instance the equality controller is the linear law $u=4(1-p)-4v$.</p>
<p>To see why the initial tests work, enforce $\nu_2\ge0$ along a closed-loop solution. Then $\dot\nu_1+2\nu_1\ge0$, so $(e^{2t}\nu_1)'\ge0$ and $\nu_1(t)\ge\nu_1(0)e^{-2t}\ge0$. In turn $\nu_1=\dot h+2h\ge0$, so $(e^{2t}h)'\ge0$ and $h(t)\ge h(0)e^{-2t}\ge0$. This is the nested HOCBF argument with linear gains $2$, and it proves that the wall is not crossed. Admissible input bounds and existence/regularity of the implemented feedback remain necessary if a different controller is used.</p>
''')

replace('exercise-19', 'Compute the safeguarding Lie derivatives, solve the destabilizing reciprocal equation and local disturbance range, derive the square-completion inflation, and state its initial-set/existence scope with a full-time bound for the specified nonnegative initial state.', r'''
<p><strong>(a) Nominal safety and local disturbance tolerance.</strong> Since $h'(x)=-1$, the drift and input derivatives are $L_fh=x$ and $L_gh=-x^2$. With $k=0$, $\dot h=x=2-h\ge-h$. Thus the linear extended class-$\mathcal K$ choice $\alpha(r)=r$ supplies the safeguarding inequality everywhere. The exact undisturbed solution $x(t)=x_0e^{-t}$ also stays at most $2$ whenever $x_0\le2$.</p>
<p>A bounded disturbance can nevertheless defeat this controller. Take $d(t)=1$ and $x_0=2$. Then $\dot x=x^2-x$ is initially $2\gt0$, immediately crossing the boundary. To compute its escape, put $y=1/x$ while $x\gt0$. The chain rule gives $\dot y=-\dot x/x^2=y-1$, with $y(0)=1/2$. Its solution is $y(t)=1-\tfrac12e^t$, hence</p>
<div class="math-block">$$x(t)=\frac1{1-\tfrac12e^t}\longrightarrow+\infty\quad\text{as }t\uparrow\ln2.$$</div>
<p>This size-one disturbance causes finite-time escape. It does not disprove <em>local</em> ISSf, which only asks for tolerance up to some sufficiently small disturbance bound.</p>
<p>For a local certificate choose $\gamma(r)=r$ and $\bar d=1/4$. Fix $r=\|d\|_\infty\le1/4$. The inflated set is $C_d=\{x\le2+r\}$. At its regular boundary $x=2+r\gt0$, the worst disturbance is $d(t)=r$, and</p>
<div class="math-block">$$\dot x\le(2+r)\big[-1+r(2+r)\big]\le(2+r)\left(-1+\frac9{16}\right)\lt0.$$</div>
<p>Thus the field points inward at this boundary for every allowed signal; the one-dimensional boundary criterion proves invariance on the solution interval. The function $\gamma(r)=r$ is class $\mathcal K$, so this supplies the requested local ISSf property. More generally, any $\bar d\lt1/2$ allows a sufficiently small positive inflation: choose $\gamma(\bar d)\lt1/\bar d-2$ and an increasing $\gamma$. For $\bar d\ge1/2$, a constant positive disturbance of that size points outward at every upper boundary $2+\gamma(\bar d)\gt2$, so this type of local inflated-set guarantee cannot extend to those bounds.</p>
<p><strong>(b) Add the constructive ISSf correction.</strong> The scalar row $L_gh=-x^2$ equals its own transpose, so $k(x)=-x^2$. With $u=-x^2+d(t)$,</p>
<div class="math-block">$$\dot x=-x-x^4+x^2d(t),\qquad\dot h=x+x^4-x^2d(t).$$</div>
<p>Complete the square in $x^2$:</p>
<div class="math-block">$$x^4-x^2d=\left(x^2-\frac d2\right)^2-\frac{d^2}{4}\ge-\frac{d^2}{4}.$$</div>
<p>Putting $r=\|d\|_\infty$ gives the requested $\dot h\ge x-r^2/4$. Since $x=2-h$, this also implies $\dot h\ge-h-r^2/4$. Define $\eta=h+r^2/4$, with $r$ a fixed bound on the entire signal. Then $\dot\eta=\dot h\ge-\eta$, and an integrating factor gives $\eta(t)\ge\eta(0)e^{-t}$. Consequently</p>
<div class="math-block">$$C_d=\left\{x:2-x+\frac{r^2}{4}\ge0\right\}=\left\{x:x\le2+\frac{r^2}{4}\right\}$$</div>
<p>is forward invariant for initial states in $C_d$. Its boundary also satisfies $\dot h\ge0$ and has nonzero gradient $h'=-1$, agreeing with Nagumo's criterion. Starting in the original $C$ therefore gives an upper overshoot allowance $r^2/4$.</p>
<p>As in this module's definition, invariance concerns the maximal interval on which a solution exists. For the specified $x_0=2$, the origin is also an equilibrium of the disturbed equation for every $d(t)$, and uniqueness prevents a trajectory from crossing below zero. The state remains in the compact interval $[0,2+r^2/4]$, so local existence extends to all forward time for bounded measurable $d$. The full upper half-line $C_d$ itself does not supply a compactness or forward-completeness argument for arbitrary negative starts.</p>
<p><strong>(c) Identify the ISSf functions.</strong> Use $\alpha(r)=r$, $\iota(r)=r^2/4$, and $\beta(r)=-\alpha(-r)=r$ on $r\ge0$. Thus $\gamma=\beta^{-1}\circ\iota$ is $\gamma(r)=r^2/4$. The extended $\alpha$ and nonnegative-domain $\iota,\gamma$ are increasing and vanish at zero; the latter two are unbounded. The derivative inequality is valid for any finite disturbance level, and the certified inflation tends to zero as that level tends to zero. This compares sets for different signal bounds; the supremum norm of a past-and-future signal does not drop retroactively when its current disturbance becomes zero.</p>
''')

replace('exercise-21', 'Construct a feasible plan for every allowed initial state, solve the two optimizations along the actual closed loop, prove the drift example’s finite continuation failure, and distinguish an exact terminal invariant set from a first-order sampled CBF surrogate.', r'''
<p><strong>(a) Terminal safety and feasible states.</strong> At the terminal state $0$, the terminal input $0$ belongs to $U$ and makes the successor $0$. All later states and inputs remain admissible, so Assumption 4.2 holds. The singleton can be represented by the Lipschitz inequality $a_S(x)=1+|x|\le1$.</p>
<p>For every $x\in[-1,1]$, the two-input plan $u_0=u_1=-x/2$ has $|u_i|\le1/2$, intermediate state $x/2\in X$, and terminal state $0$. Hence every state of $X$ is feasible. No initial state outside $X$ is feasible because the problem constrains its initial state as well. The feasible set is exactly $[-1,1]$.</p>
<p>From $x(0)=1$, the terminal equation is $1+u_0+u_1=0$. Both inputs are at least $-1/2$, so their sum can equal $-1$ only if each is $-1/2$. The desired input $u_L=1/2$ is rejected, and the actual first input is $-1/2$, producing $x(1)=1/2$.</p>
<p>At the next step, the unused tail $-1/2$ followed by the terminal input $0$ is a feasible full two-step candidate, producing $0,0$. This proves feasibility, but the filter reoptimizes rather than necessarily using that candidate. At $x=1/2$, write $u_1=-1/2-u_0$. Intersecting both input bounds gives $u_0\in[-1/2,0]$. The objective $|1/2-u_0|$ is smallest at the largest allowed $u_0$, namely $0$. The minimizing plan is therefore $(0,-1/2)$, and its applied first input leaves the current state at $1/2$.</p>
<p>The same optimization repeats at every later step. Thus the realized closed loop is $x(0)=1$, $x(k)=1/2$ for $k\ge1$, with inputs $u(0)=-1/2$, $u(k)=0$ for $k\ge1$. It is safe forever, although it never reaches the terminal set. A planned terminal arrival preserves the option to use a safe continuation; replanning does not commit the plant to execute every planned input.</p>
<p><strong>(b) Why the terminal condition is needed in a less capable plant.</strong> For the original integrator, $u=0$ keeps every point of $X$ in $X$. Without a terminal constraint, every $x\in X$ therefore has a safe two-step continuation, and every applied feasible first input leaves another state with that property. This system cannot provide a recursive-feasibility counterexample merely by removing the terminal set.</p>
<p>For the changed plant $x^+=x+u+0.6$, even the strongest negative input leaves a positive increment: $x^+-x\ge-0.5+0.6=0.1$. From $x(0)=0.5$, a feasible plan is $u_0=-0.2$, $u_1=-0.5$, producing states $0.9$ and $1.0$, both in $X$.</p>
<p>These are also the filter's first optimal choices when $u_L=0.5$. To permit a safe second step, the first successor $x_1=1.1+u_0$ must be at most $0.9$, since the second step adds at least $0.1$. Thus $u_0\le-0.2$. Together with $u_0\ge-0.5$, the feasible first-input interval is $[-0.5,-0.2]$; its point closest to $0.5$ is $-0.2$. At the resulting state $0.9$, a new two-step plan is impossible because its final state is at least $0.9+0.1+0.1=1.1$.</p>
<p>The stored one-step tail $-0.5$ still safely reaches $1.0$. At that state every admissible input produces a successor at least $1.1$, so no safe continuation exists. More generally, any admissible sequence satisfies $x(k)\ge x(0)+0.1k$, eventually exceeding $1$. There is no nonempty robust terminal safe set or terminal policy in these bounds. The finite two-step plan is valid for its two steps; it cannot establish indefinite safety without the missing terminal continuation assumption.</p>
<p><strong>(c) A CBF as a one-step continuation certificate.</strong> In a horizon-one interpretation, the terminal set is $C=\{h\ge0\}$. An admissible CBF feedback provides a continuation from states in $C$, and the filter restricts its first input to preserve that option. On the first-order sampled model, a CBF inequality gives</p>
<div class="math-block">$$h(x^+)\ge h(x)-\alpha(h(x))\Delta t.$$</div>
<p>If $h(x)\gt0$ and $\alpha(h(x))\lt h(x)/\Delta t$, this lower bound is positive. At $h(x)=0$, $\alpha(0)=0$ gives the nonnegative boundary value. The one-step successor is therefore again in the terminal set in this approximation, and CBF feasibility there supplies the next candidate input. That is the role analogous to a terminal safe set.</p>
<p>An actual fallback must exist within $U$. For compact $U$, one may select a maximizing barrier-rate input when it satisfies the required bound. For unrestricted inputs and nonzero control coefficient, that affine maximization is unbounded; a feasible minimum-norm input serves instead. Finally, the displayed sampled inequality neglects integration error. An exact held-input guarantee requires a verified intersample error bound or a discrete-time barrier inequality; the clock condition alone does not establish it.</p>
''')

retained={
 'book-m10-b1':'Recomputes measured-state lower clearance, held-input lower command, actuator membership, closest-input correction and worst terminal clearance; the unsafe reused command is checked explicitly.',
 'book-m10-b2':'Solves actuator/safety intersection feasibility, checks equality and the zero-clearance impossibility, and uses the adverse velocity to explain why faster sampling cannot restore missing authority or indefinite safe operation.',
 'book-m10-b3':'Computes the integrated movement allowance and total current uncertainty, derives and projects onto the new action bound, evaluates the reused-command failure and states the delay-wide speed hypothesis.',
 'exercise-10-p1':'Solves the safe-set inequality and evaluates all three barrier values, including the included zero boundary and sign convention.',
 'exercise-10-p2':'Computes the derivative and barrier rate, rearranges the half-line and substitutes the given state. It interprets the interior allowance and boundary direction.',
 'exercise-10-p3':'Identifies the nearest feasible endpoint, computes the correction and objective, and explains why every larger feasible input costs more.',
 'exercise-10-p4':'Checks both endpoint velocities and proves full trajectory containment by its explicit convex-combination representation.',
 'exercise-10-p5':'Writes the signed Lagrangian, solves both stationarity equations and active constraint, checks all KKT conditions and objective, and invokes strict convexity for uniqueness.',
 'exercise-10-p6':'Derives the state-dependent half-line and intersects it with actual actuator limits at both states; the counterexample to all-set CBF feasibility is explicit.',
 'exercise-10-p7':'Chooses the worst disturbance, derives the robust lower input and both numerical bounds, then checks equality under the adverse signal.',
 'exercise-10-p8':'Differentiates both auxiliary functions, computes the input condition and the valid first auxiliary value, then exhibits the negative initial auxiliary value at the second state.',
 'exercise-10-p9':'Solves the boundary-start trajectory, computes the vanishing gradient, and identifies the exact missing regularity hypothesis with a regular defining-function comparison.',
 'exercise-10-p10':'Solves continuous and held-input trajectories separately, locates the crossing, and derives the exact inclusive holding-time range from the decreasing affine path.',
 'exercise-10-p11':'Checks each original state/input, constructs the shifted tail plus terminal action, proves terminal invariance on the entire terminal interval and states model-agreement scope.',
 'exercise-10-p12':'Identifies the complete winning set and all admissible inputs, then removes the disturbed action with a failure successor and explains the universal disturbance requirement.',
 'exercise-16':'All integrating-factor steps are shown; the nonlinear comparison ODE and monotonicity uniqueness are precisely applied from the teaching context. The measurable-feedback discussion distinguishes existence from safety of each existing absolutely continuous solution and explains the separate Filippov conditions.',
 'exercise-17':'Complete weighted-QP KKT derivation with inactive/active cases, positive denominator, unique optimality and metric interpretation; every matrix/vector calculation in the example and the unweighted comparison is displayed.',
 'exercise-20':'Gives a checked family of distinct undiscounted fixed points, writes all three discounted state equations through four synchronous sweeps, verifies the unique fixed point and safe policy, and computes the geometric error factor.',
}

if __name__=='__main__':
 b=json.loads(BASE.read_bytes());rows=[]
 for e in b['exercises']:
  a=e['anchor'] or e['inventory_key'].split('::')[-1];body=replacement.get(a,e['solution']['html']);why=rationale.get(a,retained.get(a));assert why,a
  rows.append({'inventory_key':e['inventory_key'],'source_file':e['source_file'],'authoring_file':e['authoring_file'],'ordinal':e['ordinal'],'label':e['label'],'original_solution_sha256':e['solution']['sha256'],'decision':'replace' if a in replacement else 'retain','thoroughness_rationale':why,'replacement_html':body,'selected_solution_sha256':sha256(body.encode()).hexdigest()})
 assert len(rows)==21 and len(replacement)+len(retained)==21
 d={'schema_version':1,'status':'author_draft_requires_independent_math_depth_and_render_review','author':'solution_review_rotation','page':'SafeLearning/barriers.html','baseline':{'file':str(BASE),'sha256':sha256(BASE.read_bytes()).hexdigest()},'audience':'First-course linear algebra and single-variable calculus.','page_contract':{'file':'page_contract.md','sha256':sha256(Path('page_contract.md').read_bytes()).hexdigest(),'read_fully':True},'counts':{'exercises':21,'retain':len(retained),'replace':len(replacement)},'exercises':rows,'canonical_sources_or_coverage_records_edited':False,'new_citations':[]}
 with DEST.open('x',encoding='utf-8') as f:json.dump(d,f,indent=2,ensure_ascii=False);f.write('\n')
 print(json.dumps({'file':str(DEST),'sha256':sha256(DEST.read_bytes()).hexdigest(),'counts':d['counts']}))
