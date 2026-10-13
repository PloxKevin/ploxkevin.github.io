"""Author exact, individually assessed solution bodies; never edit teaching pages."""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[3]
BASELINE = 'book/solutions/baseline-source90/pages/primer-rl-nn.html.json'
OUT = 'book/solutions/drafts/primer-rl-nn-thorough-solutions-v1.json'
NUMBERS = 'reports/solution-review/primer-rl-nn-author-arithmetic-v1.json'


def ref(file):
    p = ROOT / file
    return {'file': file, 'sha256': sha256(p.read_bytes()).hexdigest()}


replacements = {}
rationales = {}
improvements = {}


def replace(ordinal, rationale, specific, html):
    assert ordinal not in replacements
    replacements[ordinal] = '\n' + html.strip() + '\n'
    rationales[ordinal] = rationale
    improvements[ordinal] = specific


replace(11, 'The existing values are correct but the coupled Bellman equations and their elimination should appear in the answer, not only in the hint. Show why an alternative action uses the old policy only after its first transition.', ['State both reward/continuation equations', 'Show elimination and both values', 'Distinguish one altered action from a new policy'], r'''
<p><strong>Write one equation from each starting state.</strong> Under the stated policy, leaving $A$ earns $1$ and moves to $B$, while leaving $B$ earns $0$ and moves to $A$. The future return starts one step later, so it receives the factor $\gamma=0.5$:</p>
<div class="math-block">$$V(A)=1+\tfrac12V(B),\qquad V(B)=0+\tfrac12V(A).$$</div>
<p>Substitute the second equation into the first, then solve:</p>
<div class="math-block">$$\begin{aligned}
V(A)&=1+\tfrac12\big(\tfrac12V(A)\big)=1+\tfrac14V(A),\\
\tfrac34V(A)&=1,\qquad V(A)=\tfrac43,\\
V(B)&=\tfrac12\cdot\tfrac43=\tfrac23.
\end{aligned}$$</div>
<p><strong>Evaluate the alternative only at the first step.</strong> The action-value $Q$ uses the specified alternative now, then returns to the original alternating policy. Its immediate reward is $0$ and its next state is $A$, so $Q(A,\text{stay})=0+\tfrac12V(A)=2/3$. Subtract the original value at the same state:</p>
<div class="math-block">$$A(A,\text{stay})=Q(A,\text{stay})-V(A)=\tfrac23-\tfrac43=-\tfrac23.$$</div>
<p>The negative advantage means that staying once and then resuming the original policy loses $2/3$ of discounted return. It is not the value of staying forever; that different policy would keep receiving zero.</p>
''')

replace(13, 'Make the maximisation in each backup explicit and justify why the same action always wins before computing the fixed point and errors.', ['Compare both backup candidates', 'Substitute every iterate', 'Solve and check the exact error sequence'], r'''
<p>Both actions return to the same state, so they have exactly the same continuation value. The optimal Bellman backup is therefore</p>
<div class="math-block">$$\mathcal T^*V=\max\{1+0.5V,\;2+0.5V\}=2+0.5V.$$</div>
<p>The second expression exceeds the first by $1$ for every $V$, which justifies using the reward-$2$ action in all three backups. Starting at $V_0=0$ gives</p>
<div class="math-block">$$\begin{aligned}
V_1&=2+0.5(0)=2,\\
V_2&=2+0.5(2)=3,\\
V_3&=2+0.5(3)=3.5.
\end{aligned}$$</div>
<p>The optimal value is the fixed point of this backup. Solving $V_*=2+0.5V_*$ gives $0.5V_*=2$, hence $V_*=4$. The same value follows from earning $2$ forever: $2/(1-0.5)=4$.</p>
<p>The errors at indices $0,1,2,3$ are $4,2,1,0.5$. More generally, subtracting the fixed-point equation gives $V_{k+1}-4=0.5(V_k-4)$, so $|V_k-4|=4(0.5)^k$. Each backup halves the error; the iterate itself and its remaining error are different quantities.</p>
''')

replace(14, 'Expose the inserted Bellman term and the fixed-point/contraction facts behind the residual estimate, then solve the general residual requirement.', ['Display the norm triangle inequality', 'Use the fixed point and sup-norm contraction', 'Separate value certification from policy performance'], r'''
<p><strong>Use the residual as one side of a triangle.</strong> For a finite discounted MDP, $\mathcal T^*$ is a $0.9$-contraction in the sup norm and $V^*=\mathcal T^*V^*$. Write $e=\|V-V^*\|_\infty$ and insert $\mathcal T^*V$ between the two vectors:</p>
<div class="math-block">$$\begin{aligned}
e&=\|V-\mathcal T^*V^*\|_\infty\\
&\le\|V-\mathcal T^*V\|_\infty
  +\|\mathcal T^*V-\mathcal T^*V^*\|_\infty\\
&\le0.03+0.9\|V-V^*\|_\infty=0.03+0.9e.
\end{aligned}$$</div>
<p>The first inequality is the triangle inequality; the second uses the measured residual and contraction. Subtracting $0.9e$ gives $0.1e\le0.03$, so $e\le0.3$.</p>
<p><strong>Solve for the residual needed by the new target.</strong> If the residual is $r$ instead, the same argument gives $e\le r/(1-0.9)=10r$. Therefore $r\le0.01$ is sufficient for $e\le0.1$, since $10(0.01)=0.1$. The factor $1/(1-\gamma)$ explains why a residual of $0.03$ does not mean a value error of $0.03$.</p>
<p>This is a guarantee about the whole value vector under the stated Bellman operator. A guarantee about the return of its greedy policy requires a policy-performance bound as well.</p>
''')

replace(15, 'The existing comparison needs explicit value-iteration behaviour for the terminating model, not merely its contraction factor. Derive both sequences and connect finite value to survival probabilities.', ['Show the contradictory finite Bellman equation', 'Compute both iteration sequences', 'Explain the termination-based geometric sum'], r'''
<p><strong>Model $A$: a reward on every visit forever.</strong> There is no terminal continuation to remove. Its Bellman equation is $V=1+V$, which would imply $0=1$ if $V$ were finite. Thus there is no finite value solution. Starting from $V_0=0$, the backup is $V_{k+1}=1+V_k$, giving $0,1,2,3,\ldots$ and, by induction, $V_k=k$. These iterates and the infinite undiscounted return diverge to $+\infty$.</p>
<p><strong>Model $B$: reward now, then possibly terminate.</strong> The current visit earns $1$ regardless of what happens next. With probability $1/2$ another visit follows and with probability $1/2$ the terminal state's continuation is zero. Therefore</p>
<div class="math-block">$$V=1+\tfrac12V+\tfrac12(0)
\quad\Longrightarrow\quad\tfrac12V=1
\quad\Longrightarrow\quad V=2.$$</div>
<p>From zero, value iteration gives $V_{k+1}=1+\tfrac12V_k$, so the first values are $0,1,3/2,7/4$. Iterating the recurrence sums a geometric series:</p>
<div class="math-block">$$V_k=\sum_{j=0}^{k-1}(1/2)^j=2\big(1-(1/2)^k\big)\longrightarrow2.$$</div>
<p>The same sum has a trajectory interpretation. To receive the reward on visit $j+1$, the process must survive $j$ previous transitions, with probability $(1/2)^j$. Summing these expected rewards gives $2$. The probability of surviving forever is zero.</p>
<p>The backup in model $B$ contracts by $1/2$ because only half of the next-state probability remains nonterminal. This factor comes from termination, even though there is no discount. Model $A$ has no such structure. One must check the model's termination or other uniqueness assumptions before using an undiscounted Bellman equation.</p>
''')

replace(18, 'Substitution into the natural-gradient formula gives the correct step but does not by itself explain why it maximises the linear objective. Prove optimality using a rescaled Euclidean ball and then compute the step.', ['Rescale the quadratic constraint', 'Apply Cauchy-Schwarz with its equality case', 'Verify active constraint and improvement', 'State the local-approximation limitation'], r'''
<p><strong>Write the local optimisation in coordinates.</strong> Here $g^\top\Delta=2\Delta_1+\Delta_2$ and $\Delta^\top F\Delta=4\Delta_1^2+\Delta_2^2$. Introduce $v=(2\Delta_1,\Delta_2)$. The constraint becomes $\|v\|_2^2\le0.1$ and the objective becomes $v_1+v_2=(1,1)^\top v$.</p>
<p>By Cauchy&ndash;Schwarz, $(1,1)^\top v\le\sqrt2\,\|v\|_2\le\sqrt{0.2}$. Equality requires $v$ to be a positive multiple of $(1,1)$ and to use the full allowed norm. Thus $v_1=v_2=\sqrt{0.05}$, which gives the maximising step</p>
<div class="math-block">$$\Delta^*=\sqrt{0.05}\,(1/2,1)
\approx(0.111803,0.223607).$$</div>
<p><strong>Check it in the original coordinates.</strong> The natural direction is $F^{-1}g=(2/4,1)=(1/2,1)$ and $g^\top F^{-1}g=2(1/2)+1=2$. Writing $c=\sqrt{0.05}$, we have</p>
<div class="math-block">$$\begin{aligned}
\tfrac12(\Delta^*)^\top F\Delta^*
 &=\tfrac12c^2\big(4(1/2)^2+1^2\big)=c^2=0.05,\\
g^\top\Delta^*&=2(c/2)+c=2c=\sqrt{0.2}\approx0.447214.
\end{aligned}$$</div>
<p>The step saturates the quadratic constraint and attains the proved upper bound on linear gain. This is the predicted improvement in the local model. The true reward objective and KL are nonlinear in policy parameters; a finite deployment step may therefore require a line search and a check of the actual KL.</p>
''')

replace(24, 'Show both activation regions, justify the row/column spectral norms, and prove that the exact Lipschitz constant cannot be smaller than one. State the open-ball convention for each radius.', ['Give dimensionally correct weights', 'Calculate spectral norms', 'Prove the represented map by cases', 'Check both certificate radii and the boundary tie'], r'''
<p><strong>Represent the two hidden activations.</strong> With one scalar input, take</p>
<div class="math-block">$$W_1=\begin{pmatrix}1\\-1\end{pmatrix},\qquad
W_2=\begin{pmatrix}1&-1\end{pmatrix},\qquad
f(x)=W_2\operatorname{ReLU}(W_1x).$$</div>
<p>There are no biases. The first layer outputs $(\operatorname{ReLU}(x),\operatorname{ReLU}(-x))$, and the second subtracts its second coordinate. A one-column or one-row matrix has spectral norm equal to its Euclidean vector norm, so $\|W_1\|_2=\sqrt{1^2+(-1)^2}=\sqrt2$ and $\|W_2\|_2=\sqrt2$. ReLU is $1$-Lipschitz, giving the product upper bound $\sqrt2\sqrt2=2$.</p>
<p><strong>Use the structure that this bound discards.</strong> If $x\ge0$, then $\operatorname{ReLU}(x)=x$ and $\operatorname{ReLU}(-x)=0$, so $f(x)=x$. If $x\lt0$, these activations are $0$ and $-x$, so again $f(x)=0-(-x)=x$. Consequently $|f(x)-f(y)|=|x-y|$ for every pair. A Lipschitz constant of $1$ works, and every pair of distinct inputs forces any valid constant to be at least $1$. The exact global constant is therefore $1$.</p>
<p><strong>Convert the score into a certificate.</strong> At $x=2$, $f(2)=2$ and the positive-class margin is $2$. The product bound gives $2/2=1$: every perturbation with $|\delta|\lt1$ preserves the strict positive sign. The exact constant gives $2/1=2$, certifying every $|\delta|\lt2$.</p>
<p>The decision boundary is $f(x)=x=0$, at actual distance $2$. At $\delta=-2$ the score is zero, so a strict-sign certificate includes every smaller radius but not that boundary point. The tighter bound recovers this exact boundary distance; the product bound loses the mutual structure of the two ReLU branches.</p>
''')

replace(27, 'Derive the residual-to-error estimate rather than treating a small residual as self-certifying. Show all iteration substitutions and compare the resulting bound with the exact error.', ['Solve the fixed point', 'Substitute each of the three iterates', 'Prove the contraction and residual estimate', 'Compare residual with error'], r'''
<p>For this fixed input, write $F(z)=0.5z+2$. Solving $z_*=F(z_*)$ gives $z_*=0.5z_*+2$, hence $0.5z_*=2$ and $z_*=4$. Starting from zero,</p>
<div class="math-block">$$z_1=0.5(0)+2=2,\qquad
z_2=0.5(2)+2=3,\qquad
z_3=0.5(3)+2=3.5.$$</div>
<p><strong>Measure the residual at the current iterate.</strong> One more evaluation gives $F(z_3)=0.5(3.5)+2=3.75$. Thus $r=|F(z_3)-z_3|=|3.75-3.5|=0.25$. This is the current equation mismatch, not directly the distance to its solution.</p>
<p>The map contracts because $|F(z)-F(w)|=0.5|z-w|$. Let $e=|z_3-z_*|$, use $F(z_*)=z_*$, and insert $F(z_3)$:</p>
<div class="math-block">$$\begin{aligned}
e&\le|z_3-F(z_3)|+|F(z_3)-F(z_*)|\\
 &\le r+0.5e.
\end{aligned}$$</div>
<p>Rearranging gives $0.5e\le r$, so $e\le r/(1-0.5)=0.25/0.5=0.5$. Here the actual error is $|3.5-4|=0.5$, so the certificate is exact. The contraction factor is what converts the observed residual into a guaranteed equilibrium error.</p>
''')

replace(31, 'The original budget algebra is sound, but explicitly justify optimisation over the feasible probability interval and evaluate both reward and maintenance units at the endpoint.', ['Keep the policy and discounted-budget interpretation', 'Solve the positive-denominator inequality', 'Show reward monotonicity', 'Substitute numerator, denominator and cost'], r'''
<p>Keep the lab's stationary policy family, start state $R$, transition model and discount $0.8$. Its evaluated returns are $C(p)=p/(1+0.2p)$ maintenance units and $J(p)=(2+2p)/(0.2+0.04p)$ items, with $0\le p\le1$.</p>
<p><strong>Solve the new budget.</strong> Since $1+0.2p$ is positive throughout the policy interval, multiplying preserves the inequality:</p>
<div class="math-block">$$\begin{aligned}
\frac{p}{1+0.2p}\le0.25
 &\iff p\le0.25(1+0.2p)=0.25+0.05p\\
 &\iff0.95p\le0.25\\
 &\iff p\le\frac{0.25}{0.95}=\frac5{19}.
\end{aligned}$$</div>
<p>Intersecting with $[0,1]$ leaves the full feasible interval $[0,5/19]$. To find the best member, the quotient rule gives</p>
<div class="math-block">$$J'(p)=\frac{2(0.2+0.04p)-0.04(2+2p)}{(0.2+0.04p)^2}
=\frac{0.32}{(0.2+0.04p)^2}\gt0.$$</div>
<p>Production increases with $p$, so the best feasible choice is its largest value, $p_*=5/19\approx0.263158$.</p>
<p><strong>Evaluate the selected policy.</strong> Its reward numerator is $2+2(5/19)=48/19$. Its denominator is $1/5+(1/25)(5/19)=1/5+1/95=4/19$. Therefore $J(p_*)=(48/19)/(4/19)=12$ discounted items. The maintenance check is $C(p_*)=(5/19)/(1+1/19)=(5/19)/(20/19)=1/4$ unit.</p>
<p>This is the optimum in the stipulated policy family under the known model. The expected discounted budget can hold while particular trajectories contain repairs; it is not a rule prohibiting each individual maintenance event.</p>
''')

replace(32, 'Derive the uncertain-model cost from both Bellman equations, explain monotonicity and the worst parameter, and distinguish a robust budget failure from failure under every model.', ['Expand cost-equation elimination', 'Prove the worst wear parameter', 'Solve the robust actuator-probability interval', 'Check p=0.5 and state model-interval scope'], r'''
<p><strong>Evaluate maintenance with the unknown constant wear rate.</strong> In state $R$, fast is chosen with probability $p$ and then causes wear with probability $\rho$. Thus next state is $W$ with probability $\rho p$. Repair costs one now and returns to $R$, so</p>
<div class="math-block">$$C_W=1+0.8C_R,\qquad
C_R=0.8\big[(1-\rho p)C_R+\rho pC_W\big].$$</div>
<p>There is no immediate maintenance cost in $R$. Substitute the first equation into the second:</p>
<div class="math-block">$$\begin{aligned}
C_R&=0.8\big[(1-\rho p)C_R+\rho p(1+0.8C_R)\big]\\
&=0.8\rho p+(0.8-0.16\rho p)C_R,\\
(0.2+0.16\rho p)C_R&=0.8\rho p.
\end{aligned}$$</div>
<p>The denominator is positive for $p\in[0,1]$, $\rho\in[0.2,0.3]$, giving $C(p,\rho)=C_R=0.8\rho p/(0.2+0.16\rho p)$.</p>
<p><strong>Choose the worst allowed model before solving the budget.</strong> Put $q=\rho p$. Differentiating $0.8q/(0.2+0.16q)$ gives</p>
<div class="math-block">$$\frac{0.8(0.2+0.16q)-0.16(0.8q)}{(0.2+0.16q)^2}
=\frac{0.16}{(0.2+0.16q)^2}\gt0.$$</div>
<p>For a fixed nonnegative $p$, the greatest cost is therefore at $\rho=0.3$. Its budget condition is</p>
<div class="math-block">$$\begin{aligned}
\frac{0.24p}{0.2+0.048p}\le0.5
&\iff0.24p\le0.1+0.024p\\
&\iff0.216p\le0.1\\
&\iff p\le\frac{25}{54}\approx0.462963.
\end{aligned}$$</div>
<p>Hence the largest robustly feasible probability is $25/54$, and all probabilities in $[0,25/54]$ satisfy the budget for every allowed constant wear rate.</p>
<p>At $p=0.5$, the worst cost is $0.8(0.3)(0.5)/(0.2+0.16(0.3)(0.5))=0.12/0.224=15/28\approx0.535714\gt0.5$. It fails the robust requirement because this allowed model violates the budget; this does not mean it fails under every smaller wear rate.</p>
<p>The conclusion assumes that the actual wear rate is constant and lies in the stated interval. No confidence level for an estimated interval is supplied here, and the result is still an expected discounted maintenance statement.</p>
''')

replace(33, 'Work out the combined physical uncertainty and both active ReLU terms, then distinguish the inconclusive lower bound from an actual allowed negative example and exact tie distance.', ['Add noise and fixed-bias bounds', 'Carry units through normalisation', 'Evaluate nominal and adverse inputs', 'Derive the active-region score and tie'], r'''
<p><strong>Compute the nominal score.</strong> Normalising $y_0=2.8$ mm/s gives $z_0=(2.8-2)/1=0.8$. Both ReLUs are active there, so</p>
<div class="math-block">$$m(0.8)=1.2-0.6(0.8+0.5)-0.4(0.8-0.5)
=1.2-0.78-0.12=0.3.$$</div>
<p>The nominal recommendation is positive. Write the total physical error as the sum of noise $n$ and fixed bias $b$, with $|n|\le0.2$ and $|b|\le0.15$ mm/s. The triangle inequality gives $|n+b|\le0.35$ mm/s. Division by the normalising scale $1$ mm/s gives $|z-z_0|\le0.35$, or $z\in[0.45,1.15]$.</p>
<p>The global Lipschitz bound of $m$ is $1$: each ReLU is $1$-Lipschitz, so their weighted changes are at most $(0.6+0.4)|z-z_0|$. Its resulting lower bound is $m(z)\ge0.3-0.35=-0.05$. A negative lower bound alone is inconclusive about the true score; it shows that this bound does not certify strict positivity.</p>
<p><strong>Check whether failure is actually possible.</strong> Choose allowed errors $n=+0.2$, $b=+0.15$ mm/s. Their total places the input at $y=3.15$ mm/s and $z=1.15$. For every $z\ge0.5$, the ReLUs can be removed by their active formulas:</p>
<div class="math-block">$$\begin{aligned}
m(z)&=1.2-0.6(z+0.5)-0.4(z-0.5)\\
&=1.2-0.6z-0.3-0.4z+0.2=1.1-z.
\end{aligned}$$</div>
<p>Thus $m(1.15)=1.1-1.15=-0.05$, an actual allowed negative score. The positive nomination is not robustly certified.</p>
<p><strong>Locate the tie in the positive direction.</strong> Moving up from $z_0=0.8$ remains in the region $z\ge0.5$, so the first zero is at $z=1.1$. In physical units this is $y=2+(1)(1.1)=3.1$ mm/s, a distance of $3.1-2.8=0.3$ mm/s. At that point the score is zero and the nomination rule selects A, since only a strictly positive score selects B. Any closed uncertainty interval containing it therefore fails strict-positive certification.</p>
<p>Repeated readings do not remove the unknown fixed bias. The given hard bounds also provide no statistical averaging rule that would shrink the total uncertainty automatically.</p>
''')

replace(34, 'Make the stationary balance and production averaging explicit, justify summing dependent repair indicators, and compare the different start distributions and discount conventions.', ['Write the ready-to-worn probability and transition matrix', 'Solve and check the stationary law', 'Compute each stationary reward/cost rate', 'Explain linearity over 20 shifts and the discount distinction'], r'''
<p>With $p=5/9$, the probability of becoming worn after a ready shift is $q=0.25p=(1/4)(5/9)=5/36$. A worn shift always repairs and returns to ready. In state order $(R,W)$, the transition matrix is therefore</p>
<div class="math-block">$$P=\begin{pmatrix}31/36&5/36\\1&0\end{pmatrix}.$$</div>
<p><strong>Solve the stationary balance.</strong> Let $w$ be the stationary worn probability and $1-w$ the ready probability. A next worn state can come only from a current ready state, so $w=(1-w)(5/36)$. Multiplying by $36$ and collecting terms gives $36w=5-5w$, hence $41w=5$. Thus $w=5/41$ and $1-w=36/41$; these are nonnegative and sum to one.</p>
<p>Repair occurs exactly in $W$ and costs one unit, so the mean stationary repair rate is $5/41\approx0.121951$ maintenance unit per shift. The conditional mean production in $R$ is</p>
<div class="math-block">$$2(1-p)+4p=2+2p=2+\frac{10}{9}=\frac{28}{9}.$$</div>
<p>Production in $W$ is zero. Averaging across the stationary states gives $(36/41)(28/9)+(5/41)(0)=112/41\approx2.731707$ items per shift.</p>
<p><strong>Count repairs over the specified stationary horizon.</strong> If the initial state has this stationary law, every shift has repair probability $5/41$. Let $I_t$ indicate repair. Linearity of expectation gives $\mathbb E[\sum_{t=0}^{19}I_t]=\sum_{t=0}^{19}\mathbb E[I_t]=20(5/41)=100/41\approx2.439024$. The indicators need not be independent for this expectation calculation.</p>
<p>The budget $C(5/9)=0.5$ is instead $\mathbb E[\sum_{t=0}^{\infty}0.8^tI_t]$ starting in $R$, not in stationarity. It uses a different initial distribution, an infinite horizon and geometrically decreasing weights. Twenty unweighted stationary shifts can therefore have an expected count exceeding $0.5$ without contradicting the discounted budget. Neither expectation guarantees a particular number of repairs on each individual trajectory.</p>
''')

replace(35, 'Expand every discounted-horizon and time-constant calculation, keep the requested strict below-one-percent condition, and derive the omitted-return bound from its first omitted index.', ['Establish absolute convergence before the return bound', 'Handle logarithm sign reversal and adjacent horizons', 'Convert step length to seconds', 'Use the exact tail before rounding'], r'''
<p><strong>(a) Bound every permitted trajectory.</strong> With $|r_t|\le2$ and $\gamma=0.95$, the series of absolute discounted rewards is bounded by a convergent geometric series. Thus the return exists absolutely, and</p>
<div class="math-block">$$|G|=\left|\sum_{t=0}^{\infty}0.95^tr_t\right|
\le\sum_{t=0}^{\infty}0.95^t|r_t|
\le2\sum_{t=0}^{\infty}0.95^t
=\frac2{1-0.95}=40.$$</div>
<p><strong>(b) Find the first integer with weight below one percent.</strong> The requirement is $0.95^T\lt0.01$. Taking logs gives $T\ln0.95\lt\ln0.01$. Since $\ln0.95\lt0$, division reverses the inequality:</p>
<div class="math-block">$$T\gt\frac{\ln0.01}{\ln0.95}
=\frac{\ln100}{\ln(1/0.95)}\approx89.7811.$$</div>
<p>The first integer is $T=90$. Check its neighbour: $0.95^{89}\approx0.0104088\gt0.01$ and $0.95^{90}\approx0.00988836\lt0.01$. The weights decrease thereafter, so the condition holds at all later steps. The rough effective-horizon scale $1/(1-\gamma)=20$ is not this one-percent cutoff; a stricter small tail requires several such scales.</p>
<p><strong>(c) Account for the physical sampling interval.</strong> At time $t=k\Delta t$, equality of the discrete and continuous weights requires $\gamma^k=e^{-k\Delta t/\tau}$, hence $\gamma=e^{-\Delta t/\tau}$. With $\Delta t=0.1$ s,</p>
<div class="math-block">$$\ln0.95=-\frac{0.1\ \mathrm{s}}{\tau}
\quad\Longrightarrow\quad
\tau=-\frac{0.1\ \mathrm{s}}{\ln0.95}
=\frac{0.1\ \mathrm{s}}{\ln(20/19)}\approx1.94957\ \mathrm{s}.$$</div>
<p>This is about $19.5$ sample steps, close to the scale $20$. The $90$-step cutoff is $9$ seconds, about $4.6$ time constants.</p>
<p><strong>(d) Bound the omitted return.</strong> After the first $T=90$ rewards, whose indices are $0$ through $89$, the omitted sum starts at $90$. Therefore</p>
<div class="math-block">$$\left|\sum_{t=90}^{\infty}0.95^tr_t\right|
\le2\sum_{t=90}^{\infty}0.95^t
=\frac{2(0.95)^{90}}{1-0.95}
=40(0.95)^{90}\approx0.395534.$$</div>
<p>The exact bound is below $0.40$, which is one percent of the worst-case total bound $40$. This is an absolute tail guarantee, not necessarily one percent of an individual trajectory's actual return, which may be small or cancel across time. The decimal displays are approximations to the original expressions.</p>
''')

replace(36, 'The matrix calculation is mostly complete, but expand construction from the action rules, the greedy-policy evaluation and the statewise improvement check.', ['Build transition and reward averages', 'Display the two-by-two inverse and products', 'Evaluate all action comparisons', 'Solve the new policy values before comparing'], r'''
<p><strong>(a) Average actions before forming the linear system.</strong> Under the uniform policy, rest at home gives reward $1$ and goes to home, while go gives reward $0$ and goes to the field. Return from the field gives reward $0$ and goes home, while harvest gives reward $2$ and stays in the field. Each action has probability $1/2$. Consequently</p>
<div class="math-block">$$P_\pi=\begin{pmatrix}0.5&0.5\\0.5&0.5\end{pmatrix},\qquad
r_\pi=\begin{pmatrix}0.5(1)+0.5(0)\\0.5(0)+0.5(2)\end{pmatrix}
=\begin{pmatrix}0.5\\1\end{pmatrix}.$$</div>
<p>At $\gamma=0.9$, the Bellman equation $(I-\gamma P_\pi)V=r_\pi$ has matrix</p>
<div class="math-block">$$I-0.9P_\pi=\begin{pmatrix}0.55&-0.45\\-0.45&0.55\end{pmatrix}.$$</div>
<p>Its determinant is $0.55^2-(-0.45)(-0.45)=0.3025-0.2025=0.1$. The two-by-two inverse formula swaps diagonal entries and negates off-diagonal ones, giving</p>
<div class="math-block">$$N=\frac1{0.1}\begin{pmatrix}0.55&0.45\\0.45&0.55\end{pmatrix}
=\begin{pmatrix}5.5&4.5\\4.5&5.5\end{pmatrix}.$$</div>
<p>Each row sums to $5.5+4.5=10=1/(1-0.9)$. This agrees with the interpretation of $N(s,s')$ as the expected discounted number of visits to $s'$ from $s$, whose total across all states is the full geometric sum.</p>
<p><strong>(b) Evaluate values and normalised state occupancy.</strong></p>
<div class="math-block">$$\begin{aligned}
V^\pi&=Nr_\pi
=\begin{pmatrix}5.5(0.5)+4.5(1)\\4.5(0.5)+5.5(1)\end{pmatrix}
=\begin{pmatrix}7.25\\7.75\end{pmatrix},\\
d^{\pi\top}&=0.1(1,0)N=0.1(5.5,4.5)=(0.55,0.45).
\end{aligned}$$</div>
<p>The occupancy entries are nonnegative and sum to one because the factor $1-\gamma$ normalises discounted visit counts. Starting at home explains why the first row of $N$ is used.</p>
<p><strong>(c) Improve the policy and evaluate the result.</strong> The old-policy action-values are</p>
<div class="math-block">$$\begin{aligned}
Q^\pi(1,a)&=1+0.9(7.25)=7.525,&Q^\pi(1,b)&=0+0.9(7.75)=6.975,\\
Q^\pi(2,a)&=0+0.9(7.25)=6.525,&Q^\pi(2,b)&=2+0.9(7.75)=8.975.
\end{aligned}$$</div>
<p>The larger action-value is $a$ at home and $b$ in the field. Thus $\pi'$ rests at home and harvests in the field. Under this new policy both states self-loop, so $V^{\pi'}(1)=1+0.9V^{\pi'}(1)=10$ and $V^{\pi'}(2)=2+0.9V^{\pi'}(2)=20$, where each equality to the number follows by solving its scalar equation.</p>
<p>Statewise improvement is explicit: $10-7.25=2.75\ge0$ and $20-7.75=12.25\ge0$. The policy is still not optimal at home: one more greedy step compares resting at value $10$ with going to the field at value $0.9(20)=18$, and chooses go. Improvement of both values does not mean the first improved policy is already optimal.</p>
''')

replace(37, 'Organise the four policies by their actual trajectories, prove the global home-state comparison using finite discounted optimality, and carry both optimality and cost inequalities through their intersection.', ['Evaluate every deterministic stationary policy', 'State the theorem scope justifying the comparison', 'Handle equality versus strict improvement', 'Derive the harvest-cost interval and feasible mixture interpretation'], r'''
<p><strong>(a) List policies by their two actions.</strong> Use $(\text{action at home},\text{action in the field})$. Here $a$ means rest at home or return from the field, and $b$ means go from home or harvest in the field.</p>
<ul>
<li>Under $(a,a)$, starting at home produces rewards $1,1,1,\ldots$, so $V(1)=1/(1-\gamma)$.</li>
<li>Under $(a,b)$, the trajectory from home never enters the field. Its home value is also $1/(1-\gamma)$, regardless of its unvisited field action.</li>
<li>Under $(b,b)$, the rewards are $0,h,h,\ldots$: going earns no immediate reward, then harvesting continues forever. Thus $V(1)=h\sum_{t=1}^{\infty}\gamma^t=\gamma h/(1-\gamma)$.</li>
<li>Under $(b,a)$, the trajectory alternates go and return, both with reward zero. Its home value is $0$.</li>
</ul>
<p><strong>(b) Compare complete returns.</strong> For a finite discounted MDP, an optimal deterministic stationary policy exists; hence checking these four policies suffices for the optimal value at home even though more general policies are allowed. Since $1/(1-\gamma)\gt0$, the zero-reward shuttle never wins. The relevant comparison is</p>
<div class="math-block">$$\frac{\gamma h}{1-\gamma}\ge\frac1{1-\gamma}
\quad\Longleftrightarrow\quad\gamma h\ge1,$$</div>
<p>where multiplication preserves the direction because $1-\gamma\gt0$. Leaving to harvest is optimal exactly when $\gamma h\ge1$, and strictly improves the home value exactly when $\gamma h\gt1$. At equality, both staying and leaving to harvest attain the same optimal home value.</p>
<p><strong>(c) Interpret the discount.</strong> Staying supplies a unit reward now and each later step. Leaving sacrifices that immediate reward and starts a stream of reward $h$ one step later, multiplying its whole value by $\gamma$. Thus $\gamma h$ is the one-step-delayed reward scale compared with the immediate scale $1$. For $h=2$, $\gamma=1/2$ is the tie. A smaller discount favours immediate rest; a larger one favours the future harvest stream.</p>
<p><strong>(d) Intersect reward optimality with the original cost budget.</strong> Under go-then-harvest, the costs are $0,1,1,\ldots$, so</p>
<div class="math-block">$$J_c=\sum_{t=1}^{\infty}\gamma^t=\frac{\gamma}{1-\gamma}.
\qquad
\frac{\gamma}{1-\gamma}\le\frac92
\iff\gamma\le\frac92(1-\gamma)
\iff\frac{11}{2}\gamma\le\frac92
\iff\gamma\le\frac9{11}.$$</div>
<p>With $h=2$, optimality requires $\gamma\ge1/2$. Therefore always harvest is both reward-optimal and budget-feasible exactly for $1/2\le\gamma\le9/11\approx0.818182$. At the lower endpoint it ties with resting and costs $1$; at the upper endpoint the cost is exactly $4.5$.</p>
<p>For larger discounts always harvest violates the budget. Resting is feasible, and mixing episodes or equivalently their occupancy measures permits intermediate return/cost pairs. At the running value $\gamma=0.9$, the half-rest/half-harvest episode mixture has return $14$ and cost $4.5$, as in Section 3. This mixture is distinct from averaging per-state action probabilities.</p>
''')

replace(38, 'The original minimisation is correct but compressed. Show the score derivatives, both moments and numerical variances, and give a complete square-integrability/global-optimality argument for the general baseline.', ['Derive both Bernoulli scores', 'Expand the mean cancellation and variance minimisation', 'Show all three numerical second moments', 'Verify existence of the mixed moment by Cauchy-Schwarz', 'Complete the general quadratic square'], r'''
<p><strong>(a) Compute the two possible gradient samples.</strong> For a finite logistic parameter, $0\lt p\lt1$ and $dp/d\theta=p(1-p)$. Differentiating the log probabilities gives $s(1)=p(1-p)/p=1-p$ and $s(0)=-p(1-p)/(1-p)=-p$. Therefore $g_b=(r-b)s$ equals $(1-b)(1-p)$ with probability $p$ and $bp$ with probability $1-p$. Averaging gives</p>
<div class="math-block">$$\mathbb E[g_b]
=p(1-b)(1-p)+(1-p)bp
=p(1-p)\big((1-b)+b\big)=p(1-p).$$</div>
<p>The baseline cancels from the mean for every constant $b$. Also $\mathbb E[s]=p(1-p)+(1-p)(-p)=0$.</p>
<p><strong>(b) Minimise variance by minimising the second moment.</strong> Since the mean is independent of $b$, only $\mathbb E[g_b^2]$ matters:</p>
<div class="math-block">$$\begin{aligned}
\mathbb E[g_b^2]&=p(1-b)^2(1-p)^2+(1-p)b^2p^2,\\
\frac{d}{db}\mathbb E[g_b^2]
&=-2p(1-b)(1-p)^2+2(1-p)bp^2\\
&=2p(1-p)\big(-(1-b)(1-p)+bp\big)\\
&=2p(1-p)\big(b-(1-p)\big).
\end{aligned}$$</div>
<p>The second derivative is $2p(1-p)\gt0$, so the unique global minimiser is $b^*=1-p$. At this choice, the action-$1$ sample is $p(1-p)$ and the action-$0$ sample is also $(1-p)p$. The sample is constant, so the minimal variance is exactly zero.</p>
<p><strong>(c) Substitute $p=0.8$.</strong> The mean is $0.8(0.2)=0.16$, whose square is $0.0256$.</p>
<ul>
<li>For $b=0$, the samples are $0.2$ and $0$. The second moment is $0.8(0.2^2)+0.2(0^2)=0.032$, so the variance is $0.032-0.0256=0.0064$.</li>
<li>For $b=0.8$, the samples are $(1-0.8)(0.2)=0.04$ and $0.8(0.8)=0.64$. The second moment is $0.8(0.0016)+0.2(0.4096)=0.0832$, giving variance $0.0832-0.0256=0.0576$.</li>
<li>For the optimal $b^*=0.2$, both samples equal $0.16$. The second moment is $0.0256$ and the variance is $0$.</li>
</ul>
<p>The average-reward baseline $0.8$ has variance $0.0576/0.0064=9$ times that of no baseline. Preserving the mean does not ensure variance reduction.</p>
<p><strong>(d) Prove the general formula under the stated assumptions.</strong> Since $s$ and $rs$ are square-integrable, $g_b=rs-bs$ is square-integrable for every finite constant $b$. Their mixed moment exists too: Cauchy&ndash;Schwarz gives $\mathbb E[|rs^2|]\le\sqrt{\mathbb E[r^2s^2]\mathbb E[s^2]}\lt\infty$. The mean is $\mathbb E[g_b]=\mathbb E[rs]-b\mathbb E[s]=\mathbb E[rs]$, independent of $b$.</p>
<p>Write $A=\mathbb E[s^2]\gt0$, $B=\mathbb E[rs^2]$ and $K=\mathbb E[r^2s^2]$. Expanding and completing the square gives</p>
<div class="math-block">$$\begin{aligned}
\operatorname{Var}(g_b)
&=K-2bB+b^2A-\big(\mathbb E[rs]\big)^2\\
&=A\left(b-\frac BA\right)^2
 +K-\frac{B^2}{A}-\big(\mathbb E[rs]\big)^2.
\end{aligned}$$</div>
<p>Only the nonnegative square depends on $b$, and its coefficient is strictly positive. Thus the unique minimum is at $b^*=B/A=\mathbb E[rs^2]/\mathbb E[s^2]$. In the Bernoulli example, $B=p(1-p)^2$ and $A=p(1-p)^2+(1-p)p^2=p(1-p)$, yielding $b^*=1-p$. The squared scores determine the baseline's weighting; it is generally different from the mean reward.</p>
''')

replace(39, 'Make both policy evaluations and occupancy laws explicit, and distinguish the well-defined known-model sum surrogate from the invalid importance-ratio representation under missing support.', ['Evaluate old values, Q and advantages', 'Derive old and new discounted state occupancies', 'Compute the performance-difference sum', 'Explain the two distinct support failures'], r'''
<p><strong>(a) Evaluate the old policy.</strong> Rest everywhere means action $a$ in both states: stay home with reward $1$, or return from the field with reward $0$. Consequently $V^\pi(1)=1+0.9V^\pi(1)=10$ after solving, and $V^\pi(2)=0+0.9(10)=9$. Each action-value takes its named action once and follows this old policy afterwards:</p>
<div class="math-block">$$\begin{aligned}
Q^\pi(1,a)&=1+0.9(10)=10,&Q^\pi(1,b)&=0+0.9(9)=8.1,\\
Q^\pi(2,a)&=0+0.9(10)=9,&Q^\pi(2,b)&=2+0.9(9)=10.1.
\end{aligned}$$</div>
<p>Subtracting the state's old value gives $A^\pi(1,\cdot)=(10-10,8.1-10)=(0,-1.9)$ and $A^\pi(2,\cdot)=(9-9,10.1-9)=(0,1.1)$.</p>
<p><strong>(b) Use the state distribution of the new policy.</strong> Under $\pi'$ the trajectory is at home at $t=0$ and in the field at every $t\ge1$, always taking action $b$. The normalised discounted occupancy is therefore</p>
<div class="math-block">$$d^{\pi'}(1)=0.1,\qquad
d^{\pi'}(2)=0.1\sum_{t=1}^{\infty}0.9^t=0.1\frac{0.9}{0.1}=0.9.$$</div>
<p>The performance-difference lemma uses these new state weights with the old advantages:</p>
<div class="math-block">$$\begin{aligned}
J(\pi')-J(\pi)
&=\frac1{1-0.9}\big(0.1(-1.9)+0.9(1.1)\big)\\
&=10(-0.19+0.99)=8.
\end{aligned}$$</div>
<p>Directly, $J(\pi')=2\sum_{t=1}^{\infty}0.9^t=18$ and $J(\pi)=\sum_{t=0}^{\infty}0.9^t=10$, so their difference is also $8$.</p>
<p><strong>(c) Replace those weights by the old ones.</strong> Starting at home, the old policy stays there forever, giving $d^\pi=(1,0)$. The sum-form surrogate, using the known action-values from (a), is</p>
<div class="math-block">$$L_\pi(\pi')=J(\pi)+\frac1{1-\gamma}
\sum_sd^\pi(s)\sum_a\pi'(a\mid s)A^\pi(s,a)
=10+10\big(1(-1.9)+0(1.1)\big)=-9.$$</div>
<p>This is a surrogate objective, not the true return $18$. It counts the old disadvantage of leaving home but gives no weight to harvesting in the field, because that state is never visited by the old policy. The state-distribution substitution removes the entire source of the new policy's improvement.</p>
<p>There is a second support issue if we try to estimate the same sum through old-action samples. At home $\pi'(b\mid1)=1$ but $\pi(b\mid1)=0$, so the required ratio $\pi'(b\mid1)/\pi(b\mid1)$ is undefined. Old samples contain only $a$ at home, with advantage zero. Naively averaging their defined ratio-weighted advantages gives zero and hence $10$, not even the known-model sum $-9$. It cannot represent the missing action's contribution.</p>
<p>Without additional model information, collecting more of the same old-policy data cannot reveal the untried action or its subsequent field outcomes. This is why support matters in off-policy evaluation and why large policy changes make an old-distribution surrogate unreliable.</p>
''')

replace(40, 'Present the clipping branches and derivatives in a comparison table, then work through residuals, backward GAE, the Monte-Carlo limit and the finite lambda-return mixture.', ['Evaluate clipped and unclipped terms separately', 'State derivatives away from clip endpoints', 'Show all residual and backward substitutions', 'Verify the TD return by both baseline and finite-mixture identities'], r'''
<p><strong>(a) Identify the active reward branch.</strong> Let $c(\varrho)=\operatorname{clip}(\varrho,0.8,1.2)$. The reward term is the smaller of $\varrho\hat A$ and $c(\varrho)\hat A$. Multiplying by a negative advantage reverses which branch is smaller.</p>
<table><thead><tr><th>$(\varrho,\hat A)$</th><th>$\varrho\hat A$</th><th>$c(\varrho)\hat A$</th><th>Reward term</th><th>Derivative in $\varrho$</th></tr></thead><tbody>
<tr><td>$(1.3,1)$</td><td>$1.3$</td><td>$1.2$</td><td>$1.2$</td><td>$0$</td></tr>
<tr><td>$(0.7,1)$</td><td>$0.7$</td><td>$0.8$</td><td>$0.7$</td><td>$1$</td></tr>
<tr><td>$(0.7,-1)$</td><td>$-0.7$</td><td>$-0.8$</td><td>$-0.8$</td><td>$0$</td></tr>
<tr><td>$(1.3,-1)$</td><td>$-1.3$</td><td>$-1.2$</td><td>$-1.3$</td><td>$-1$</td></tr>
</tbody></table>
<p>The two zero derivatives occur when the selected branch is constant in a neighbourhood of the stated ratio. The other two use the unclipped branch. These ratios are away from the switching points $0.8$ and $1.2$, where a derivative may fail to exist. Clipping caps the benefit of favourable moves while charging adverse moves in full; it does not force the policy ratio to stay inside the interval.</p>
<p><strong>(b) Use the maximum for pessimistic cost.</strong> At $(0.7,1)$, the candidates are $0.7$ and $0.8$, giving $\max(0.7,0.8)=0.8$. At $(1.3,-1)$, they are $-1.3$ and $-1.2$, giving $-1.2$. In both cases the clipped cost term is at least its unclipped counterpart, limiting the credited cost reduction. This comparison is between surrogate terms, not a certificate of the true future cost.</p>
<p><strong>(c) Form the TD residuals first.</strong> The terminal state's value is zero. With $V_0=0.5,V_1=0.6,V_2=0.8$ along this episode,</p>
<div class="math-block">$$\begin{aligned}
\delta_0&=0+0.9(0.6)-0.5=0.04,\\
\delta_1&=0+0.9(0.8)-0.6=0.12,\\
\delta_2&=1+0.9(0)-0.8=0.2.
\end{aligned}$$</div>
<p>For $\lambda=0.5$, the multiplier is $\gamma\lambda=0.45$. Start with zero advantage after termination and work backwards:</p>
<div class="math-block">$$\begin{aligned}
\hat A_2&=0.2,\\
\hat A_1&=0.12+0.45(0.2)=0.21,\\
\hat A_0&=0.04+0.45(0.21)=0.1345.
\end{aligned}$$</div>
<p>For $\lambda=1$, the time-zero sum is $\delta_0+0.9\delta_1+0.9^2\delta_2=0.04+0.108+0.162=0.31$. The critic terms telescope, giving the same result as the complete discounted return minus the starting baseline: $0+0.9(0)+0.9^2(1)-0.5=0.31$.</p>
<p>The TD($0.5$) return adds the starting critic value back to GAE, so $G_0^\lambda=0.5+0.1345=0.6345$. One can check this using the finite three-step mixture. Its one-, two- and three-step targets are $G_0^{(1)}=0.54$, $G_0^{(2)}=0.9^2(0.8)=0.648$ and $G_0^{(3)}=0.9^2(1)=0.81$. The terminal mixture weights at $\lambda=0.5$ are $0.5,0.25,0.25$, giving $0.5(0.54)+0.25(0.648)+0.25(0.81)=0.27+0.162+0.2025=0.6345$. The final weight includes the complete return, rather than bootstrapping beyond termination.</p>
''')

replace(41, 'Calculate exact exponential weights before decimals, verify the variational identity algebraically and numerically, and qualify the safety conflict by unsafe actions within the policy support.', ['Compute probabilities and soft values at both temperatures', 'Derive and check the soft maximum bounds', 'Expand the exact KL identity', 'Prove the zero-temperature limit', 'State full-support safety conditions'], r'''
<p><strong>(a) Normalise exponential scores for probabilities.</strong> For $Q=(0,1)$ and temperature $\alpha\gt0$, the weights are $(1,e^{1/\alpha})$. Thus</p>
<div class="math-block">$$\mathrm{softmax}_\alpha(Q)
=\left(\frac1{1+e^{1/\alpha}},\frac{e^{1/\alpha}}{1+e^{1/\alpha}}\right),\qquad
\mathrm{LSE}_\alpha(Q)=\alpha\ln(1+e^{1/\alpha}).$$</div>
<p>At $\alpha=0.5$, the weights are $(1,e^2)$ with $e^2\approx7.389056$, so the probabilities are approximately $(0.119203,0.880797)$ and the soft value is $0.5\ln(1+e^2)\approx1.063464$. At $\alpha=1$, the weights are $(1,e)$ with $e\approx2.718282$, so the probabilities are approximately $(0.268941,0.731059)$ and the value is $\ln(1+e)\approx1.313262$.</p>
<p>Factoring out $e^{1/\alpha}$ rewrites the soft value as $1+\alpha\ln(1+e^{-1/\alpha})$. Since $0\lt e^{-1/\alpha}\lt1$, it lies between $1$ and $1+\alpha\ln2$. Numerically, $1\le1.063464\le1.346574$ for $\alpha=0.5$, and $1\le1.313262\le1.693147$ for $\alpha=1$. The probabilities and the scalar soft value serve different roles.</p>
<p><strong>(b) Verify with the exact softmax law.</strong> The uniform $p=(1/2,1/2)$ has $p^\top Q=1/2$ and entropy $\mathcal H(p)=-2(\tfrac12\ln\tfrac12)=\ln2$. Hence the left side is $1/2+(1/2)\ln2\approx0.846574$. Put $D=1+e^2$ and $p^*=(1/D,e^2/D)$. Expanding the KL gives</p>
<div class="math-block">$$\begin{aligned}
D_{\rm KL}(p\|p^*)
&=\tfrac12\ln\frac{1/2}{1/D}+\tfrac12\ln\frac{1/2}{e^2/D}\\
&=\tfrac12(\ln D-\ln2)+\tfrac12(\ln D-2-\ln2)\\
&=\ln D-1-\ln2\approx0.433781.
\end{aligned}$$</div>
<p>The right side therefore simplifies exactly to</p>
<div class="math-block">$$\tfrac12\ln D-\tfrac12(\ln D-1-\ln2)
=\tfrac12+\tfrac12\ln2,$$</div>
<p>the same expression as the left side. Numerically, $1.063464-0.5(0.433781)\approx0.846574$. The uniform policy is below the optimal soft value by $\alpha D_{\rm KL}\approx0.216890$. Rounded probabilities are displays, not replacements for the exact atoms in this identity.</p>
<p><strong>(c) Take the zero-temperature limit.</strong> The bound $1\le\mathrm{LSE}_\alpha(Q)\le1+\alpha\ln2$ squeezes the value to $1=\max Q$ as $\alpha\to0^+$. Also $e^{-1/\alpha}\to0$, so the probabilities $(e^{-1/\alpha}/(1+e^{-1/\alpha}),1/(1+e^{-1/\alpha}))$ tend to $(0,1)$. The unique highest-valued action becomes greedy. With tied highest scores, the limit is uniform over the maximisers.</p>
<p><strong>(d) Check which actions remain possible.</strong> At every positive temperature and finite score, each available action has positive probability. If a visited state has an available action that reaches an unsafe state with positive probability, assigning that action positive mass prevents a guarantee of never taking the unsafe transition. Merely making its probability small does not make it zero. An unconstrained softmax over such actions therefore conflicts with hard safety; applying softmax only over actions already certified safe is a different, restricted action set. Full support is not itself a problem when all available actions are safe.</p>
''')

replace(42, 'The original nearest-boundary result omits the proof that the other branch is farther. Derive every possible zero-score branch and minimise each distance, then fully work the interval and normalisation certificates.', ['Compute the complete forward pass', 'Derive both boundary branches from ReLU cases', 'Minimise both squared distances', 'Propagate both interval pre-activations', 'Distinguish closed local certification and open global radius', 'Convert the normalised centre and radius to pixel space'], r'''
<p><strong>(a) Evaluate the network at the stated input.</strong> The worked map is $f(x)=\operatorname{ReLU}(x_1+x_2-1)-2\operatorname{ReLU}(x_1-x_2)-1$. At $x=(-2,0)$,</p>
<div class="math-block">$$v_1=\begin{pmatrix}-2+0-1\\-2-0\end{pmatrix}
=\begin{pmatrix}-3\\-2\end{pmatrix},\qquad
z_1=\begin{pmatrix}0\\0\end{pmatrix},\qquad f(x)=0-2(0)-1=-1.$$</div>
<p>The negative class has margin $|f(x)|=1$. The global Lipschitz bound $L=\sqrt{10}$ therefore certifies strict sign preservation whenever $\|\delta\|_2\lt1/\sqrt{10}\approx0.316228$.</p>
<p><strong>(b) Find the entire decision boundary before taking a distance.</strong> Write $u=x_1+x_2-1$ and $v=x_1-x_2$. A boundary point satisfies $\operatorname{ReLU}(u)-2\operatorname{ReLU}(v)-1=0$.</p>
<ul>
<li>If $v\le0$, the second ReLU is zero and the equation requires $\operatorname{ReLU}(u)=1$. Thus $u=1$, or $x_1+x_2=2$, with $x_1\le x_2$. Parameterise this branch by $(t,2-t)$, $t\le1$.</li>
<li>If $v\gt0$, the equation requires $\operatorname{ReLU}(u)=1+2v\gt0$, so the first ReLU is active as well. Substituting gives $x_1+x_2-1-2(x_1-x_2)-1=0$, or $x_1=3x_2-2$. The condition $v=2x_2-2\gt0$ gives $x_2\gt1$. Including the common endpoint describes the second branch by $(3t-2,t)$, $t\ge1$.</li>
</ul>
<p>These cases cover every zero of the score. On the first branch, the squared distance from $(-2,0)$ is</p>
<div class="math-block">$$(t+2)^2+(2-t)^2=2t^2+8.$$</div>
<p>It is minimised at $t=0$, which obeys $t\le1$. The nearest point on that branch is $(0,2)$ and its distance is $\sqrt8=2\sqrt2$. On the second branch, the squared distance is $((3t-2)-(-2))^2+t^2=(3t)^2+t^2=10t^2\ge10$ for $t\ge1$. Its nearest endpoint $(1,1)$ has distance $\sqrt{10}\gt\sqrt8$. Therefore the true distance to the whole decision boundary is $2\sqrt2\approx2.828427$.</p>
<p>The global radius uses the steepest region's slope $\sqrt{10}$ even though both neurons are inactive near this input and the local score is the constant $-1$. The actual boundary distance is $2\sqrt2\sqrt{10}=4\sqrt5\approx8.94$ times the global certified radius. A global worst-case slope can thus be valid and very conservative here.</p>
<p><strong>(c) Propagate the full input box.</strong> On $x_1\in[-3,-1]$, $x_2\in[-1,1]$, the affine pre-activation bounds are</p>
<div class="math-block">$$\begin{aligned}
x_1+x_2-1&\in[-3-1-1,\;-1+1-1]=[-5,-1],\\
x_1-x_2&\in[-3-1,\;-1-(-1)]=[-4,0].
\end{aligned}$$</div>
<p>Neither interval has a positive value. ReLU maps both to the singleton $\{0\}$, including zero at an endpoint, so the entire box has $f=-1$ and is strictly classified negative. This box is the closed $\ell_\infty$ ball of radius $1$ around $(-2,0)$. Every perturbation with $\|\delta\|_2\le1$ also has $\|\delta\|_\infty\le1$, so it lies in the box. This local calculation certifies the closed Euclidean ball of radius $1$, about $\sqrt{10}$ times the global radius. It still need not reach the exact distance $2\sqrt2$.</p>
<p><strong>(d) Convert the input space, including its centre.</strong> The normalised centre $\tilde x=(-2,0)$ corresponds to pixel-space centre $x=0.5\tilde x=(-1,0)$. A physical perturbation $\delta$ becomes $\delta/0.5=2\delta$ inside the network. Thus the composite map is $2\sqrt{10}$-Lipschitz in pixel space, with the same score margin $1$ at its corresponding centre. Its global pixel-space radius is</p>
<div class="math-block">$$\frac1{2\sqrt{10}}=\frac{0.5}{\sqrt{10}}\approx0.158114,$$</div>
<p>again with strict sign preservation for smaller Euclidean perturbations. Quoting the normalised radius as a pixel-space radius would miss this factor of two.</p>
''')

RETAIN = {
    1: 'The existing answer multiplies each reward by its probability, adds the expectation, and checks the full set of possible individual outcomes. It directly distinguishes a policy average from a trajectory.',
    2: 'The geometric ratio and scaling are explicit, the finite partial-sum formula is supplied, and its limit and the need for discounting are explained. The requested series is fully evaluated.',
    3: 'Both partial derivatives state which argument is held fixed, substitute the requested point and explain parameter sensitivity versus input sensitivity. No further chain-rule step is hidden.',
    4: 'All four instantaneous regrets, their cumulative total, the average division and the recommendation-only regret are supplied. The use of true means and the two different objectives are stated.',
    5: 'Every upper/lower confidence arithmetic substitution is present. The solution first compares unconstrained reward optimism, then certified actions, then the constrained choice; joint band validity and uncertified versus unsafe are explicit.',
    6: 'The learner and both fixed-arm totals are calculated, followed by the dynamic comparator total and each regret difference. The changing-objective and comparator meanings are explained.',
    7: 'Both discounted returns show each reward weight, reset the time origin for G1 and numerically verify the Bellman split. The terminal continuation is zero.',
    8: 'The fixed-action transition average, its discounted action-value and the policy average are all explicitly evaluated. It identifies the two separate sources of averaging and keeps the immediate reward undiscounted.',
    9: 'The two complete violation-count distributions give both expected counts and any-violation probabilities. The answer explains why these trajectory events differ and retains the undiscounted finite-horizon scope.',
    10: 'The scalar Bellman equation is solved by subtraction and checked independently against the geometric return. The fixed-point and trajectory interpretations are connected.',
    12: 'The normalised occupancy is derived from the geometric normaliser, both reward/cost returns include the 1/(1-gamma) factor, and the budget plus reward monotonicity identify and evaluate the optimum. Expected-cost scope is clear.',
    16: 'The expected reward derivative uses dp/dtheta with its full numerical substitution; each score is computed and the probability-weighted zero-score identity is checked. These are all the requested quantities.',
    17: 'Both advantages, their zero mean and the complete score-weighted gradient sum are worked numerically. The equality to the direct derivative and the action-independent baseline condition are explained.',
    19: 'Target, TD error and partial learning-rate update each show their numerical substitution; nonterminal versus terminal continuation and moving partway to the target are explained.',
    20: 'The exact exponential weights are normalised to the two probabilities, the exact soft value and hard maximum are compared, and their log gap is supplied. It explains the entropy objective and avoids equating the soft value to ordinary mean reward.',
    21: 'The mixture mean, within-model variance and between-mean variance are separately computed. Two observationally identical environments with opposite unseen rewards demonstrate why ensemble agreement is not a performance certificate.',
    22: 'Both dot products, biases, ReLU outputs and dimensions are explicitly calculated. The ordering of affine map and activation is explained.',
    23: 'The forward pass and loss are computed, then the output derivative is propagated through the active ReLU and affine pre-activation to all four requested derivatives. Parameter and input gradient roles are distinguished.',
    25: 'All three windows and their difference outputs are listed; each shared pair of weights appears in the implementing matrix. Orientation, dimensions and the convolution/cross-correlation distinction are explicit.',
    26: 'For both branches the full residual map is simplified before computing its exact scalar slope and comparing with the standard sum bound. Cancellation and the absence of an automatic contraction guarantee are explained.',
    28: 'The winning class and runner-up margin are computed, then both rival gaps include the simultaneous worst downward/upward logit changes. Strict positivity of each gap proves unchanged prediction.',
    29: 'The score and exact Lipschitz constant give the radius, the zero-score equation yields the actual boundary distance, and the open versus closed strict-sign distinction is checked by an explicit boundary perturbation.',
    30: 'The multiclass radius specifies Euclidean norms and strict preservation. Certified examples give the lower bound, clean errors plus found counterexamples give the disjoint upper-bound exclusions, and failed attacks are not treated as proofs.',
}

assert len(replacements) == 19 and len(RETAIN) == 23
assert set(replacements).isdisjoint(RETAIN)
assert set(replacements) | set(RETAIN) == set(range(1,43))
assert not (ROOT / OUT).exists() and not (ROOT / NUMBERS).exists(), 'Use fresh immutable artifact names'
baseline = json.loads((ROOT / BASELINE).read_bytes())
assert len(baseline['exercises']) == 42
assert ref(baseline['source']['file'])['sha256'] == baseline['source']['sha256']
rows = []
for b in baseline['exercises']:
    ordinal = b['ordinal']
    decision = 'replace' if ordinal in replacements else 'retain'
    html = replacements.get(ordinal, b['solution']['html'])
    row = {
        'inventory_key': b['inventory_key'], 'source_file': b['source_file'],
        'authoring_file': b['authoring_file'], 'ordinal': ordinal,
        'anchor': b['anchor'], 'label': b['label'],
        'original_source_sha256': b['source_sha256'],
        'original_authoring_source_sha256': b['authoring']['source_sha256'],
        'original_question_sha256': b['problem']['sha256'],
        'original_hint_sha256': [h['disclosure']['sha256'] for h in b['hints']],
        'original_solution_sha256': b['solution']['sha256'],
        'decision': decision, 'replacement_html': html,
        'replacement_sha256': sha256(html.encode()).hexdigest(),
        'baseline_adequacy': 'already_complete_for_requested_scope' if decision == 'retain' else 'correct_but_selected_steps_are_too_compressed',
        'thoroughness_rationale': rationales[ordinal] if decision == 'replace' else RETAIN[ordinal],
        'specific_improvements': improvements.get(ordinal, []),
        'whole_question_hint_answer_and_background_read': True,
        'pedagogical_status': 'authored_pending_independent_review',
        'question_hint_disclosure_notation_anchor_preservation_required': True,
    }
    rows.append(row)

# Actual author recomputation; these are supplementary arithmetic receipts, not
# formal proofs, independent peer approval, or a compiler-success claim.
checks = []
def check(name, actual, expected=None, exact=False):
    if expected is not None:
        assert actual == expected, name
    checks.append({'name': name, 'actual': str(actual), 'expected': str(expected) if expected is not None else None, 'exact_rational': exact})

check('E.S8 cycle VA', F(1)/(1-F(1,2)**2), F(4,3), True)
check('E.S8 cycle VB', F(1,2)*F(4,3), F(2,3), True)
check('E.S8 alternative advantage', F(1,2)*F(4,3)-F(4,3), -F(2,3), True)
check('E.S11 value-error bound', F(3,100)/(1-F(9,10)), F(3,10), True)
check('E.S15 predicted gain squared', F(4)*F(5,100), F(1,5), True)
check('E.S24 residual', F(1,2)*F(7,2)+2-F(7,2), F(1,4), True)
check('E.S24 error', F(1,4)/(1-F(1,2)), F(1,2), True)
J = lambda p: (2+2*p)/(F(1,5)+F(1,25)*p)
C = lambda p: p/(1+F(1,5)*p)
check('E.B1 optimum production', J(F(5,19)), F(12), True)
check('E.B1 optimum maintenance', C(F(5,19)), F(1,4), True)
uncertain_cost = lambda p,rho: F(4,5)*rho*p/(F(1,5)+F(4,25)*rho*p)
check('E.B2 robust endpoint cost', uncertain_cost(F(25,54),F(3,10)), F(1,2), True)
check('E.B2 half-policy worst cost', uncertain_cost(F(1,2),F(3,10)), F(15,28), True)
score = lambda z: F(6,5)-F(3,5)*max(F(0),z+F(1,2))-F(2,5)*max(F(0),z-F(1,2))
check('E.B3 nominal score', score(F(4,5)), F(3,10), True)
check('E.B3 adverse score', score(F(23,20)), -F(1,20), True)
check('E.B3 exact tie score', score(F(11,10)), F(0), True)
check('E.B4 stationary repair fraction', F(5,36)/(1+F(5,36)), F(5,41), True)
check('E.B4 stationary production', F(36,41)*(2+2*F(5,9)), F(112,41), True)
check('E.B4 expected 20 repairs', 20*F(5,41), F(100,41), True)
gamma=F(19,20)
assert gamma**89 > F(1,100) > gamma**90
check('E.1 exact preceding weight', gamma**89, exact=True)
check('E.1 exact qualifying weight', gamma**90, exact=True)
check('E.1 logarithmic cutoff', math.log(100)/math.log(20/19))
check('E.1 seconds time constant', 0.1/math.log(20/19))
check('E.1 exact omitted-tail bound', 40*gamma**90, exact=True)
assert 40*gamma**90 < F(2,5)
check('E.1 displayed tail float', float(40*gamma**90))
P=[[F(1,2),F(1,2)],[F(1,2),F(1,2)]]
N=[[F(11,2),F(9,2)],[F(9,2),F(11,2)]]
A=[[(1 if i==j else 0)-F(9,10)*P[i][j] for j in range(2)] for i in range(2)]
assert [[sum(A[i][k]*N[k][j] for k in range(2)) for j in range(2)] for i in range(2)] == [[1,0],[0,1]]
check('E.2 exact inverse product identity', '[[1,0],[0,1]]', '[[1,0],[0,1]]', True)
check('E.2 value home', F(11,2)*F(1,2)+F(9,2), F(29,4), True)
check('E.2 value field', F(9,2)*F(1,2)+F(11,2), F(31,4), True)
check('E.3 maximal feasible discount', F(9,2)/(1+F(9,2)), F(9,11), True)
p=F(4,5)
for b,target in [(F(0),F(64,10000)),(F(4,5),F(576,10000)),(F(1,5),F(0))]:
    mean=p*(1-p)
    m2=p*((1-b)*(1-p))**2+(1-p)*(b*p)**2
    check('E.4 variance at baseline '+str(b),m2-mean**2,target,True)
check('E.5 exact performance difference', 10*(F(1,10)*-F(19,10)+F(9,10)*F(11,10)), F(8), True)
check('E.5 known-model old-state surrogate', 10+10*-F(19,10), F(-9), True)
d=[F(4,100),F(12,100),F(2,10)]
mult=F(9,10)*F(1,2)
advantages=[F(0)]*3
for t in range(2,-1,-1):advantages[t]=d[t]+mult*(advantages[t+1] if t<2 else 0)
assert advantages == [F(1345,10000),F(21,100),F(1,5)]
check('E.6 exact backward advantages',str(advantages),str([F(1345,10000),F(21,100),F(1,5)]),True)
check('E.6 lambda-one advantage',sum(F(9,10)**t*d[t] for t in range(3)),F(31,100),True)
check('E.6 lambda return',F(1,2)+advantages[0],F(6345,10000),True)
check('E.6 finite mixture check', F(1,2)*F(54,100)+F(1,4)*F(648,1000)+F(1,4)*F(81,100),F(6345,10000),True)
for alpha in [0.5,1.0]:
    q0=1/(1+math.exp(1/alpha));q1=1-q0;v=alpha*math.log1p(math.exp(1/alpha))
    assert 1 < v < 1+alpha*math.log(2)
    check('E.7 alpha '+str(alpha)+' probabilities',(q0,q1))
    check('E.7 alpha '+str(alpha)+' value',v)
kl=math.log1p(math.exp(2))-1-math.log(2)
lhs=0.5+0.5*math.log(2);rhs=0.5*math.log1p(math.exp(2))-0.5*kl
assert abs(lhs-rhs)<1e-14
check('E.7 exact-law KL numerical evaluation',kl)
check('E.7 variational identity numerical sides',(lhs,rhs))
check('E.8 first-branch distance squared at minimiser', F(8), F(8), True)
check('E.8 second-branch minimal distance squared', F(10), F(10), True)
check('E.8 global radius',1/math.sqrt(10))
check('E.8 actual boundary distance',2*math.sqrt(2))
check('E.8 pixel radius',0.5/math.sqrt(10))

number_report={'status':'passed_author_arithmetic_and_exact_rational_recomputations','author':'/root/review_gaussian35',
               'created_at_utc':datetime.now(timezone.utc).isoformat(),'page':'primer-rl-nn.html',
               'helper':ref('book/solutions/drafts/build-primer-rl-nn-thorough-v1.py'),
               'checks':checks,'limits':'Author-side arithmetic receipt only; not independent pedagogical approval, compiler evidence or formal coverage promotion.'}
(ROOT/NUMBERS).parent.mkdir(parents=True,exist_ok=True)
(ROOT/NUMBERS).write_text(json.dumps(number_report,ensure_ascii=False,indent=2)+'\n')
report={
    'schema':'individual_solution_draft_v1', 'status':'authored_pending_independent_review',
    'author':'/root/review_gaussian35','created_at_utc':datetime.now(timezone.utc).isoformat(),
    'page':'primer-rl-nn.html','audience':'First-course linear algebra and single-variable calculus; explain additional local RL, probability and neural-network concepts.',
    'baseline':ref(BASELINE),'baseline_manifest':ref('book/solutions/baseline-source90/manifest.json'),
    'inventory':baseline['inventory'],'page_contract':ref('page_contract.md'),
    'page_contract_fully_read':True,'criteria':ref('book/solutions/README.md'),
    'source_refs':[ref('SafeLearning/primer-rl-nn.html'),ref('book/chapters/primer-rl-nn.html')],
    'context_read':['Full canonical teaching text for all9 sections, definitions, assumptions, examples, certificates, comparisons and application context',
                    'Both policy-gradient and backpropagation interactive derivation data',
                    'Full authored application lab, including known-transition, sensor, timing, cost and units assumptions',
                    'All42 complete questions, hints and original solutions'],
    'counts':{'reviewed_exercises':42,'replace':19,'retain':23,'book_lab_exercises':4},
    'exercises':rows,'arithmetic_report':ref(NUMBERS),
    'new_external_citations':[],'independent_pedagogical_approval_claimed':False,
    'rendered_qa_claimed':False,'whole_page_reserialized':False,
    'canonical_source_owner_selection_progress_publication_mutations':False,
    'scope':'Exact solution-body proposals only. Preserve all existing questions, hints, disclosures, anchors, scripts, hooks, notation and final qualified Source90 facts. Lab replacements must be mirrored to the authored book source in the candidate. Root-appointed independent review and integration remain required.',
    'helper':ref('book/solutions/drafts/build-primer-rl-nn-thorough-v1.py'),
}
(ROOT/OUT).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'draft':ref(OUT),'arithmetic':ref(NUMBERS),'counts':report['counts']},ensure_ascii=False))
