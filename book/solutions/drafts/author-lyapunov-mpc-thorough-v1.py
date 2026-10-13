"""Prepare complete Lyapunov/MPC Source90 solution decisions."""
from pathlib import Path
from hashlib import sha256
import json

BASE=Path('book/solutions/baseline-source90/pages/lyapunov-mpc.html.json')
DEST=Path('book/solutions/drafts/lyapunov-mpc-thorough-solutions-v1.json')
replacement={}
rationale={}

def replace(a,why,body):
 replacement[a]=body.strip()+'\n';rationale[a]=why

replace('exercise-18', 'Derive both Hoeffding sample bounds, the exact integer failure threshold, both repeated-attempt sample sizes, and the two distinct probability levels and terminal-controller scope of a passed fixed validation.', r'''
<p><strong>(a) Sample size at empirical success fraction $0.998$.</strong> The desired lower success bound is $\mu_{\rm crit}=0.99$, so the available empirical margin is $0.998-0.99=0.008$. With $n$ validation trajectories, the paper's two-sided radius is $r_2(n)=\sqrt{\ln(2/\delta_h)/(2n)}$. Requiring $r_2(n)\le0.008$, squaring nonnegative quantities and rearranging gives</p>
<div class="math-block">$$n\ge\frac{\ln(2/\delta_h)}{2(0.008)^2}=\frac{\ln200}{0.000128}\approx41393.1044.$$</div>
<p>Round up to $41\,394$ trajectories. Only overestimating the success probability can falsely accept the controller, so a one-sided radius also suffices: $r_1(n)=\sqrt{\ln(1/\delta_h)/(2n)}$. It gives $n\ge\ln100/0.000128\approx35977.8921$, hence $35\,978$ trajectories.</p>
<p>These sizes make the confidence radius no larger than $0.008$. The actual batch must still attain the corresponding empirical success threshold. A predicted or approximate $0.2\%$ failure rate does not force every sampled batch to pass.</p>
<p><strong>(b) Maximum failures in $34\,980$ runs.</strong> Use the paper's two-sided radius:</p>
<div class="math-block">$$r_2=\sqrt{\frac{\ln200}{2(34980)}}\approx0.008702501.$$</div>
<p>If $m$ runs fail, the empirical success fraction is $1-m/34980$. The acceptance inequality is $1-m/34980-r_2\ge0.99$, or $m\le34980(0.01-r_2)\approx45.3865$. Because $m$ is an integer, at most $45$ failures are allowed, meaning at least $34980-45=34\,935$ successes. With $45$ failures the success fraction is approximately $0.9987136$, above the required $0.9987025$; with $46$ failures it is approximately $0.9986850$, below it. A success fraction rounded to $0.9987$ is not enough to decide this exact boundary.</p>
<p><strong>(c) Five training-and-validation attempts.</strong> Give each attempt failure budget $\delta_{m attempt}=0.01/5=0.002$, hence per-attempt confidence $0.998$. For each controller, freeze it before drawing its new IID validation batch. Conditional on the training history, that fresh batch obeys the same Hoeffding bound. Averaging over that history and taking a union bound makes the chance of any false acceptance among at most five attempts no more than $5(0.002)=0.01$. Independence between attempts is not needed for the union bound; the fresh fixed-controller validation assumptions are needed for each individual bound.</p>
<p>For the same empirical margin $0.008$, both sizes in part (a) change:</p>
<table><thead><tr><th>Bound</th><th>Required real-valued size</th><th>Rounded up</th></tr></thead><tbody><tr><td>Two-sided</td><td>$\ln1000/0.000128\approx53966.8381$</td><td>$53\,967$</td></tr><tr><td>One-sided</td><td>$\ln500/0.000128\approx48551.6258$</td><td>$48\,552$</td></tr></tbody></table>
<p>The two-sided size rises by about $30\%$, and the one-sided size by about $35\%$. Keeping the original per-attempt level $0.01$ would only supply the weaker union-bound error budget $0.05$ for five attempts.</p>
<p><strong>(d) What acceptance establishes.</strong> For a fixed controller and validation protocol, define success of a fresh initial condition from $\Omega$ to mean that its trajectory enters $X_f$ in finite time and that $\|\pi_{\rm approx}(x)-\pi_{\rm MPC}(x)\|_\infty\le\eta$ holds at every preceding step. Let $\mu$ be the probability of this event under the same initial-condition distribution. Hoeffding gives a confidence statement about $\mu$: except on a validation-sampling event of probability at most $\delta_h$, a passed test implies $\mu\ge0.99$. With the budget in part (c), the implication is valid simultaneously over all five possible acceptances at total confidence at least $0.99$.</p>
<p>On each such successful trajectory, the robust-MPC theorem supplies constraint satisfaction while the approximation error remains within its designed allowance. Upon entry to $X_f$, switch to the certified terminal controller $k_f$, which preserves its constraints and gives convergence. Thus the conclusion concerns this switched controller and at least a $0.99$ fraction of initial conditions drawn from $\Omega$, with the stated validation confidence. The approximate network was not validated inside $X_f$; using it there, or changing the initial distribution, requires additional evidence. A finite validation implementation fixes a maximal horizon and counts non-entry by that deadline as failure, as specified in Section 6.</p>
''')

replace('exercise-20', 'Work the transient-chain policy evaluation, expected visits, auxiliary-cost LP proof and both Lyapunov value systems; derive each allowed policy mixture and the true feasibility limit using exact fractions.', r'''
<p>Set every value to zero at terminal state $T$. Write $V_i=V_c^{\pi_B}(s_i)$ and $L_i=L_\epsilon(s_i)$ for the three transient states. The baseline transient transition matrix is</p>
<div class="math-block">$$P_B=\begin{bmatrix}0&1/5&4/5\\0&0&1/2\\0&1/10&0\end{bmatrix}.$$</div>
<p><strong>(a) Constraint values and visits.</strong> Policy evaluation $V=c+P_BV$ gives $V_3=V_2/10$ and $V_2=1+V_3/2$. Substitute the first into the second: $V_2=1+V_2/20$, so $(19/20)V_2=1$. Thus</p>
<div class="math-block">$$V_2=\frac{20}{19},\qquad V_3=\frac2{19},\qquad V_1=\frac15\frac{20}{19}+\frac45\frac2{19}=\frac{28}{95}.$$</div>
<p>The baseline is feasible because $28/95\approx0.294737\lt d=1/2$. Its unused budget is $b=1/2-28/95=39/190$.</p>
<p>Let $v_i$ be the expected number of visits to $s_i$ when starting at $s_1$. There is no return to $s_1$, so $v_1=1$. Counting incoming visits gives $v_2=1/5+v_3/10$ and $v_3=4/5+v_2/2$. Substitution yields $v_2=1/5+2/25+v_2/20=7/25+v_2/20$. Therefore</p>
<div class="math-block">$$(v_1,v_2,v_3)=\left(1,\frac{28}{95},\frac{18}{19}\right),\qquad \mathbb E[T^*]=1+\frac{28}{95}+\frac{18}{19}=\frac{213}{95}.$$</div>
<p>These are also the first row of $(I-P_B)^{-1}$. The loop $s_2\to s_3\to s_2$ has probability $(1/2)(1/10)=0.05$, so arbitrarily many loops are possible, although their probabilities tend geometrically to zero. Absorption occurs almost surely with finite expected time. This is enough for the finite-chain policy evaluation and LP here; it does not meet the paper's stronger assumption of a uniform deterministic termination-time bound. No claim requiring that stronger bound is used.</p>
<p><strong>(b) Optimize the auxiliary costs.</strong> Since $L=V+(I-P_B)^{-1}\epsilon$, the budget at the start becomes the LP</p>
<div class="math-block">$$\max_{\epsilon\ge0}\ \epsilon_1+\epsilon_2+\epsilon_3\quad\text{s.t.}\quad\epsilon_1+\frac{28}{95}\epsilon_2+\frac{18}{19}\epsilon_3\le\frac{39}{190}.$$</div>
<p>The smallest positive coefficient is $28/95$, belonging to $s_2$. Every feasible vector obeys $(28/95)(\epsilon_1+\epsilon_2+\epsilon_3)\le b$, so its objective is at most $b/(28/95)=39/56$. That maximum is attained by putting all auxiliary cost there: $\epsilon=(0,39/56,0)$.</p>
<p>For any auxiliary vector, $L=c+\epsilon+P_BL$ reads</p>
<div class="math-block">$$L_2=1+\epsilon_2+\frac12L_3,\quad L_3=\epsilon_3+\frac1{10}L_2,\quad L_1=\epsilon_1+\frac15L_2+\frac45L_3.$$</div>
<p>At the LP vertex, $L_3=L_2/10$ and $(19/20)L_2=1+39/56=95/56$. Hence $L_2=25/14$, $L_3=5/28$, and $L_1=(1/5)(25/14)+(4/5)(5/28)=1/2$. The resulting vector is $L=(1/2,25/14,5/28)$, and it uses the full start-state budget.</p>
<p><strong>(c) A constant auxiliary cost.</strong> Set $\epsilon_i=e$ for every transient state. The total extra start cost is $e\mathbb E[T^*]$, so the largest allowed constant is</p>
<div class="math-block">$$e=\frac{39/190}{213/95}=\frac{13}{142}\approx0.0915493.$$</div>
<p>Now $L_3=e+L_2/10$. Insert it into $L_2=1+e+L_3/2$ to obtain $(19/20)L_2=1+(3/2)e=323/284$. Thus $L_2=85/71$, $L_3=13/142+(1/10)(85/71)=15/71$, and $L_1=e+(1/5)L_2+(4/5)L_3=1/2$. This gives $L=(1/2,85/71,15/71)$.</p>
<p><strong>(d) Policy mixtures admitted by each certificate.</strong> At $s_1$, let the new policy choose $a'$ with probability $p$ and $a_B$ with probability $1-p$, where $0\le p\le1$. Section 3 defines $Q_L(s,a)=c(s)+\epsilon(s)+\sum_{s'}P(s'|s,a)L(s')$. Since the baseline chooses $a_B$, the local constraint reduces to</p>
<div class="math-block">$$p\big[Q_L(s_1,a')-Q_L(s_1,a_B)\big]\le\epsilon_1.$$</div>
<p>The other two states have only one action, already feasible because $T_{\pi_B,c}L=L-\epsilon\le L$.</p>
<p>For the LP vertex, $\epsilon_1=0$, $Q_L(s_1,a_B)=L_1=1/2$, and $Q_L(s_1,a')=(3/5)L_2=(3/5)(25/14)=15/14$. The difference is $4/7\gt0$, so $p(4/7)\le0$ permits only $p=0$. The objective-maximizing LP allocated its slack at the hazard state, where no policy choice is available, leaving none where the faster action could be introduced.</p>
<p>For constant $e=13/142$, $Q_L(s_1,a_B)=L_1=1/2$, while $Q_L(s_1,a')=e+(3/5)L_2=13/142+51/71=115/142$. Their difference is $22/71$. Thus</p>
<div class="math-block">$$p\le\frac{13/142}{22/71}=\frac{13}{44}\approx0.295455.$$</div>
<p>To compare with actual feasibility, the values at $s_2,s_3$ stay $20/19,2/19$ under either start-state choice. The baseline start cost is $28/95$; the faster action's cost is $(3/5)(20/19)=12/19=60/95$. Therefore the true cost of the mixture is</p>
<div class="math-block">$$V_c^\pi(s_1)=(1-p)\frac{28}{95}+p\frac{60}{95}=\frac{28+32p}{95}.$$</div>
<p>Solving $(28+32p)/95\le1/2$ gives $p\le39/64=0.609375$. At the constant-certificate limit $p=13/44$, the actual cost is $412/1045\approx0.394258\lt1/2$. At $p=1$ it is $12/19\gt1/2$ and is infeasible. Thus the two Lyapunov limits, $0$ and $13/44$, are conservative compared with the true feasible limit $39/64$: their local inequalities are sufficient budget certificates, not necessary conditions for a feasible policy.</p>
''')

retained={
 'book-m11-b1':'Solves the invariant-radius equation with the combined error, subtracts that radius from both physical interval endpoints, and checks the entire state band using its worst one-step magnitude.',
 'book-m11-b2':'Substitutes the accuracy target into the invariant-tube inequality, solves the exact uniform approximation allowance, tightens nominal states and explains why a distribution average cannot establish the pointwise requirement.',
 'book-m11-b3':'Computes the exceptional interval probability, squared average, square root and supremum error, then applies independence to the missed-event probability. It distinguishes loss of a specific uniform certificate from proof of actual closed-loop failure.',
 'exercise-11-p1':'Computes successor-value decrease, both sublevel endpoints and their image, and identifies the necessary zero-decrease exception at the equilibrium.',
 'exercise-11-p2':'Expands the weighted quadratic, determines both axis radii and evaluates both supplied points with exact weighted sums.',
 'exercise-11-p3':'Forms the full successor intervals and their largest squared values at both states, computes the decrease at 0.4 and explains the loss of an invariant origin under absolute disturbance.',
 'exercise-11-p4':'Computes discounted next budget plus immediate cost, subtracts for the slack and correctly interprets the expectation rather than a trajectory-level Lyapunov conclusion.',
 'exercise-11-p5':'Adds uncertainty and spatial margins for both grid radii, computes strict certified decrease in the first case and inconclusiveness in the second, and states region/norm validity.',
 'exercise-11-p6':'Uses separate worst-case triangle inequalities for the error update, actual state and corrected input, giving exact invariant radius and both nominal tightenings.',
 'exercise-11-p7':'Differentiates the convex scalar objective, computes the unconstrained root and constrained endpoint, checks successor and full objective value, and distinguishes finite-horizon optimization from stability.',
 'exercise-11-p8':'Evaluates the Hoeffding radius and percentage, compares the requested one-percent target and states IID/fixed-controller/fixed-size assumptions.',
 'exercise-11-p9':'Expands and factors the nonlinear decrease, solves the exact strict sublevel range, proves convergence by an impossible uniform loss at a positive limit, and exhibits the endpoint two-cycle.',
 'exercise-11-p10':'Proves geometric convergence by the relative-error triangle bound and induction, gives the equivalent Lyapunov decrease, and exhibits a compatible nonzero equilibrium under the absolute bound.',
 'exercise-11-p11':'Solves both logarithmic inequalities with integer ceiling, uses explicit per-controller failure allocation and states the selection restriction. Minimality of 299 and sufficiency of 597 were numerically checked.',
 'exercise-11-p12':'Applies the robust implication on the learned-set event, combines both missing-coverage events without independence and explains the need for uniform state/trajectory scope.',
 'exercise-16':'Complete compact-sublevel invariance and convergence proof, including the uniform negative maximum and the final positive-definite compactness step. The discontinuous-map counterexample and exact unattained-supremum failure are worked out.',
 'exercise-17':'All three parts already have the stacked-norm composition derivation, both numerical grid tests, integral representation and add/subtract proof of the sharper sampled-map bound, with segment-domain and norm conditions explicit.',
 'exercise-19':'Evaluates the one-variable logarithmic scenario condition, exact binomial-tail integer boundary and conservative formula; derives corrected and printed validation sizes and their Hoeffding confidence, then states the fixed-batch Bayesian implication and distribution.',
}

if __name__=='__main__':
 b=json.loads(BASE.read_bytes());rows=[]
 for e in b['exercises']:
  a=e['anchor'] or e['inventory_key'].split('::')[-1];body=replacement.get(a,e['solution']['html']);why=rationale.get(a,retained.get(a));assert why,a
  rows.append({'inventory_key':e['inventory_key'],'source_file':e['source_file'],'authoring_file':e['authoring_file'],'ordinal':e['ordinal'],'label':e['label'],'original_solution_sha256':e['solution']['sha256'],'decision':'replace' if a in replacement else 'retain','thoroughness_rationale':why,'replacement_html':body,'selected_solution_sha256':sha256(body.encode()).hexdigest()})
 assert len(rows)==20 and len(replacement)+len(retained)==20
 d={'schema_version':1,'status':'author_draft_requires_independent_math_depth_and_render_review','author':'solution_review_rotation','page':'SafeLearning/lyapunov-mpc.html','baseline':{'file':str(BASE),'sha256':sha256(BASE.read_bytes()).hexdigest()},'audience':'First-course linear algebra and single-variable calculus.','page_contract':{'file':'page_contract.md','sha256':sha256(Path('page_contract.md').read_bytes()).hexdigest(),'read_fully':True},'counts':{'exercises':20,'retain':len(retained),'replace':len(replacement)},'exercises':rows,'canonical_sources_or_coverage_records_edited':False,'new_citations':[]}
 with DEST.open('x',encoding='utf-8') as f:json.dump(d,f,indent=2,ensure_ascii=False);f.write('\n')
 print(json.dumps({'file':str(DEST),'sha256':sha256(DEST.read_bytes()).hexdigest(),'counts':d['counts']}))
