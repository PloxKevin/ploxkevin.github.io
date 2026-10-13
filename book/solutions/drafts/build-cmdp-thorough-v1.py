"""Author twenty-one exact CMDP decisions while preserving every native source."""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from statistics import NormalDist
import json
import math

ROOT = Path(__file__).resolve().parents[3]
BASELINE = 'book/solutions/baseline-source90/pages/cmdp.html.json'
OUT = 'book/solutions/drafts/cmdp-thorough-solutions-v1.json'
ARITHMETIC = 'reports/solution-review/cmdp-author-arithmetic-v1.json'
baseline = json.loads((ROOT/BASELINE).read_bytes())


def ref(file):
    return {'file': file, 'sha256': sha256((ROOT/file).read_bytes()).hexdigest()}


replacements = {}
rationales = {}
improvements = {}


def replace(n, why, specific, html):
    assert n not in replacements
    replacements[n] = '\n'+html.strip()+'\n'
    rationales[n] = why
    improvements[n] = specific


replace(1, 'Show the complete budget inequality and endpoint substitution, then justify the unchanged multiplier from the slope of the optimal value and the inner Lagrangian.', ['Solve the feasible probability interval', 'Evaluate both returns', 'Derive the marginal budget price', 'Keep the expectation-versus-entry distinction'], r'''
<p>In the lab's one-state model at discount $0.9$, the evaluated returns are $J_r(p)=20+30p$ and $J_c(p)=0.2+1.8p$, with $p\in[0,1]$ the fast-mode probability. The new budget gives</p>
<div class="math-block">$$0.2+1.8p\le0.65
\iff1.8p\le0.45
\iff p\le\frac{0.45}{1.8}=\frac14.$$</div>
<p>Thus the feasible range is $[0,1/4]$. Since reward increases with slope $30\gt0$, its largest value is at $p^*=1/4$. Substitution gives $J_r(p^*)=20+30(1/4)=27.5$ reward points and $J_c(p^*)=0.2+1.8(1/4)=0.2+0.45=0.65$ discounted entries. The constraint is active.</p>
<p><strong>Interpret the multiplier within the interior budget range.</strong> For any $0.2\lt d\lt2$, the optimal fast probability is $(d-0.2)/1.8$, lying strictly between the two pure modes. Hence</p>
<div class="math-block">$$P^*(d)=20+30\frac{d-0.2}{1.8},\qquad
\frac{dP^*}{dd}=\frac{30}{1.8}=\frac{50}{3}.$$</div>
<p>The same price follows from $L=20+30p-\lambda(0.2+1.8p-d)$: an interior maximizing mixture requires its slope $30-1.8\lambda$ to vanish. Thus $\lambda^*=50/3$ at both the old budget and $0.65$. Tightening changes how much fast mode can be used, while the marginal reward per unit cost remains constant in this model and budget range.</p>
<p>At the selected mixture, the expected one-step entry indicator is $0.02+0.18(1/4)=0.065$, still positive. Satisfying an expected discounted budget does not exclude individual exclusion-zone entries.</p>
''')

replace(2, 'Expand the changed geometric normalisation, solve the new budget and show how keeping a numerical budget changes its allowable per-step cost.', ['Recompute reward and cost at the new discount', 'Solve feasibility before maximising', 'Check the reused old probability', 'Explain a concrete budget-rescaling choice'], r'''
<p>Changing the discount keeps the one-step expectations $2+3p$ for reward and $0.02+0.18p$ for cost, but changes the total geometric weight. At $\gamma=0.95$, $1/(1-\gamma)=20$, so</p>
<div class="math-block">$$J_r(p)=\frac{2+3p}{0.05}=40+60p,\qquad
J_c(p)=\frac{0.02+0.18p}{0.05}=0.4+3.6p.$$</div>
<p>Keeping $d=1$, solve $0.4+3.6p\le1$: this gives $3.6p\le0.6$, hence $p\le0.6/3.6=1/6$. Reward has positive slope $60$, so the best feasible choice is $p^*=1/6$. Its return is $40+60(1/6)=50$ reward points, and its cost is $0.4+3.6(1/6)=1$.</p>
<p><strong>Check the proposed reuse instead of assuming feasibility transfers.</strong> For the old $p=4/9$, the new cost is $0.4+3.6(4/9)=0.4+1.6=2\gt1$. It violates the unchanged numerical budget.</p>
<p>The budget bounds a weighted cumulative count. In this stationary one-state example, its equivalent one-step expected-cost allowance is $(1-\gamma)d$: it was $0.1$ and is now $0.05$. Thus changing the discount while keeping $d=1$ halves this allowance. If the intended operational allowance were to remain $0.1$, the new budget would instead be $d=0.1/0.05=2$, restoring the old feasible probability limit. The designer must decide which physical requirement is intended.</p>
<p>The reward totals at the two discounts also have different weightings. A larger discounted total is not by itself evidence of a more productive policy under a common horizon or per-decision criterion.</p>
''')

replace(3, 'Show both admissibility comparisons, carry the exact fractions through the remaining-budget update, and verify spend/remainder at the original time origin.', ['Compare each deterministic cost with the current-time budget', 'Expand the fractional update', 'Compute discounted spend and remainder', 'State the scope for uncertain costs'], r'''
<p>The update $z_3=(z_2-c_2)/0.9$ preserves a nonnegative remainder exactly when $c_2\le z_2$, since division is by a positive number. Here $z_2=14/27\approx0.518519$. The cost $0.5=1/2$ is permitted, while $0.6=3/5$ is larger than the available amount and is not.</p>
<p>For the admissible cost, keep exact fractions through the update:</p>
<div class="math-block">$$\begin{aligned}
z_3&=\frac{14/27-1/2}{9/10}
=\frac{28/54-27/54}{9/10}\\
&=\frac1{54}\frac{10}{9}=\frac5{243}.
\end{aligned}$$</div>
<p>The preceding costs were $c_0=0.4$ and $c_1=0.2$. Measured from time zero, total spend after the new cost is $0.4+0.9(0.2)+0.9^2(0.5)=0.4+0.18+0.405=0.985$, leaving $1-0.985=0.015$. Convert the rescaled remainder back:</p>
<div class="math-block">$$0.9^3z_3=\left(\frac9{10}\right)^3\frac5{243}
=\frac{729}{1000}\frac5{243}=\frac{15}{1000}=0.015.$$</div>
<p>Spend and original-time remainder sum to the initial budget $1$. For comparison, taking cost $0.6$ would give spend $0.58+0.81(0.6)=1.066\gt1$, a genuine overspend.</p>
<p>These are deterministic realized costs. With uncertain action costs, a pathwise requirement must account for the allowed realizations, rather than plugging their expectation into the remaining-budget test. The bookkeeping variable records past spend; the policy must still choose an admissible continuation.</p>
''')

replace(12, 'Derive and compare the two dual branches, show the minimizing price and use complementary slackness explicitly to recover the policy from its flat inner problem.', ['Compute endpoint inner objectives', 'Identify each dual branch', 'Locate and verify the dual optimum', 'Apply feasibility and complementary slackness'], r'''
<p><strong>Maximize the inner affine objective.</strong> The Lagrangian is</p>
<div class="math-block">$$L(p,\lambda)=2+6p-\lambda(4p-1)
=2+\lambda+(6-4\lambda)p.$$</div>
<p>If $\lambda\lt3/2$, its slope in $p$ is positive and the maximum is at $p=1$, giving $8-3\lambda$. If $\lambda\gt3/2$, the slope is negative and the maximum is at $p=0$, giving $2+\lambda$. At $\lambda=3/2$ it is flat in $p$. Thus</p>
<div class="math-block">$$D(\lambda)=\max\{2+\lambda,8-3\lambda\}
=\begin{cases}8-3\lambda,&0\le\lambda\le3/2,\\
2+\lambda,&\lambda\ge3/2.
\end{cases}$$</div>
<p>The first branch decreases with slope $-3$, and the second increases with slope $1$. Their meeting point solves $8-3\lambda=2+\lambda$, or $4\lambda=6$. Therefore $\lambda^*=3/2$ uniquely minimizes $D$ and $D(\lambda^*)=2+3/2=7/2$.</p>
<p><strong>Recover the primal mixture.</strong> At this price, $6-4\lambda^*=0$, so every $p\in[0,1]$ has the same Lagrangian value $7/2$. Choosing $p=1$ is infeasible, while choosing $p=0$ is feasible but earns only $2$. Inner maximization alone cannot distinguish them.</p>
<p>Primal feasibility requires $4p\le1$. Complementary slackness requires $\lambda^*(4p-1)=0$. Since $\lambda^*\gt0$, the latter forces $4p-1=0$, hence $p^*=1/4$. It has $J_c=1$ and $J_r=2+6(1/4)=7/2$, agreeing with the dual optimum. Feasibility and slackness supply the information that the flat penalized objective lacks.</p>
''')

replace(15, 'The weak-duality proof is already close to complete; add the defining subgradient inequality from an exact inner maximizer so the descent sign is derived rather than asserted.', ['Prove the upper bound for every feasible policy', 'Pass to the feasible supremum without an attainment assumption', 'Derive the dual subgradient inequality', 'Project the descent step and interpret its sign'], r'''
<p><strong>Find the sign for a feasible policy first.</strong> Feasibility means $J_c(\pi)-d\le0$. For every $\lambda\ge0$, multiplication gives $-\lambda(J_c(\pi)-d)\ge0$, so</p>
<div class="math-block">$$D(\lambda)=\sup_{\pi'}L(\pi',\lambda)
\ge L(\pi,\lambda)=J_r(\pi)-\lambda(J_c(\pi)-d)
\ge J_r(\pi).$$</div>
<p>This holds for every feasible $\pi$. Taking their supremum gives $D(\lambda)\ge P^*$, whether or not that feasible supremum is attained. The tightest dual upper bound is therefore obtained by minimizing $D$ over nonnegative multipliers.</p>
<p><strong>Derive a descent direction from an exact inner maximizer.</strong> Assume $\pi_\lambda$ attains $D(\lambda)=L(\pi_\lambda,\lambda)$. For any other nonnegative $\lambda'$,</p>
<div class="math-block">$$\begin{aligned}
D(\lambda')&\ge L(\pi_\lambda,\lambda')\\
&=L(\pi_\lambda,\lambda)+(d-J_c(\pi_\lambda))(\lambda'-\lambda)\\
&=D(\lambda)+g(\lambda'-\lambda),\qquad g=d-J_c(\pi_\lambda).
\end{aligned}$$</div>
<p>This is the definition of a subgradient $g$ of the convex dual function. It need not be an ordinary derivative when several inner policies maximize the Lagrangian, as at a dual kink.</p>
<p>For a positive step $\eta$, subtract that subgradient and project back to $[0,\infty)$:</p>
<div class="math-block">$$\lambda^+=[\lambda-\eta g]_+
=[\lambda+\eta(J_c(\pi_\lambda)-d)]_+.$$</div>
<p>A positive upper-budget violation increases the multiplier and makes cost more expensive in the next policy objective. Slack decreases the price, but projection prevents a negative penalty. This is dual descent in the reward-maximization convention; no sign rule needs to be memorized independently of the Lagrangian.</p>
''')

replace(16, 'Display the index-shift and flow derivation line by line, state the finite/bounded hypotheses that justify the LP and exchanges, and explain realization and convex mixtures.', ['State the model and sum-exchange conditions', 'Prove mass and linear returns', 'Show each flow/index step', 'Write the full LP', 'Explain bounded polytope and policy recovery', 'Demonstrate convexity of achievable pairs'], r'''
<p>Work in the finite-state, finite-action discounted CMDP of this section, with $0\lt\gamma\lt1$, initial probability law $\mu$, and bounded rewards and costs. The policy may be history-dependent; the Markov transition law still conditions the next state on its current state-action pair.</p>
<p><strong>(a) Normalize the visits and evaluate reward.</strong> At each $t$, exactly one state-action pair occurs, so its joint probabilities sum to one. Consequently</p>
<div class="math-block">$$\begin{aligned}
\sum_{s,a}\rho_\pi(s,a)
&=(1-\gamma)\sum_{t=0}^{\infty}\gamma^t
   \sum_{s,a}\Pr_\mu^\pi(s_t=s,a_t=a)\\
&=(1-\gamma)\sum_{t=0}^{\infty}\gamma^t=1.
\end{aligned}$$</div>
<p>The terms here are nonnegative, so exchanging sums is valid. For reward, boundedness $|r|\le B_r$ gives $\mathbb E\sum_t\gamma^t|r_t|\le B_r/(1-\gamma)\lt\infty$, justifying the signed sum/expectation exchange. Hence</p>
<div class="math-block">$$\begin{aligned}
J_r(\pi)&=\sum_{t=0}^{\infty}\gamma^t
\sum_{s,a}\Pr_\mu^\pi(s_t=s,a_t=a)r(s,a)\\
&=\sum_{s,a}r(s,a)\sum_{t=0}^{\infty}\gamma^t\Pr_\mu^\pi(s_t=s,a_t=a)\\
&=\frac1{1-\gamma}\sum_{s,a}\rho_\pi(s,a)r(s,a)
=\frac{\langle\rho_\pi,r\rangle}{1-\gamma}.
\end{aligned}$$</div>
<p>The identical argument with $c_i$ gives each cost return.</p>
<p><strong>(b) Separate initial mass from incoming mass.</strong> Put $\rho_\pi(s)=\sum_a\rho_\pi(s,a)$. The Markov law gives $\Pr(s_{t+1}=s)=\sum_{s',a'}\Pr(s_t=s',a_t=a')P(s\mid s',a')$. Insert it in the portion of occupancy after time zero, with index $u=t+1$:</p>
<div class="math-block">$$\begin{aligned}
\rho_\pi(s)
&=(1-\gamma)\mu(s)+(1-\gamma)\sum_{u=1}^{\infty}\gamma^u\Pr(s_u=s)\\
&=(1-\gamma)\mu(s)+(1-\gamma)\sum_{t=0}^{\infty}\gamma^{t+1}
  \sum_{s',a'}\Pr(s_t=s',a_t=a')P(s\mid s',a')\\
&=(1-\gamma)\mu(s)+\gamma\sum_{s',a'}P(s\mid s',a')
  (1-\gamma)\sum_{t=0}^{\infty}\gamma^t\Pr(s_t=s',a_t=a')\\
&=(1-\gamma)\mu(s)+\gamma\sum_{s',a'}\rho_\pi(s',a')P(s\mid s',a').
\end{aligned}$$</div>
<p>Only nonnegative probability terms are rearranged in this derivation.</p>
<p><strong>(c) Change the optimization variable to occupancy.</strong> The finite CMDP is the linear program</p>
<div class="math-block">$$\begin{aligned}
\max_{\rho\ge0}\quad&\frac{\langle\rho,r\rangle}{1-\gamma}\\
\text{s.t.}\quad&\langle\rho,c_i\rangle\le(1-\gamma)d_i\quad\text{for each }i,\\
&\sum_a\rho(s,a)-\gamma\sum_{s',a'}\rho(s',a')P(s\mid s',a')
=(1-\gamma)\mu(s)\quad\text{for each }s.
\end{aligned}$$</div>
<p>All its expressions are linear in finitely many variables. To check boundedness rather than just assert it, sum the flow equations over $s$. Transition probabilities sum to one and $\mu$ has mass one, giving $M=1-\gamma+\gamma M$ for $M=\sum_{s,a}\rho(s,a)$. Since $1-\gamma\gt0$, $M=1$. Nonnegativity then bounds each entry between zero and one. A bounded set cut out by finitely many linear equalities and inequalities is a polytope.</p>
<p>The occupancy completeness theorem ensures this is exactly the policy problem: every policy has these flows, and each flow-feasible $\rho$ is realized by $\pi_\rho(a\mid s)=\rho(s,a)/\sum_b\rho(s,b)$ at positive-occupancy states. At zero-occupancy states any action distribution may be specified. The resulting state marginal solves the same invertible system with $I-\gamma P_{\pi_\rho}$, so its actual occupancy equals $\rho$.</p>
<p><strong>(d) Show convexity in the correct variable.</strong> Let $\rho_1,\rho_2$ be achievable occupancies and $\kappa\in[0,1]$. The convex combination $\rho_\kappa=\kappa\rho_1+(1-\kappa)\rho_2$ remains nonnegative and satisfies the same flow equalities, so it is realized by a policy. Linearity from (a) gives</p>
<div class="math-block">$$(J_r,J_c)(\rho_\kappa)
=\kappa(J_r,J_c)(\rho_1)+(1-\kappa)(J_r,J_c)(\rho_2).$$</div>
<p>Thus every line segment between two achievable return/cost pairs is achievable. This uses the flow polytope without imposing a particular budget; intersecting with cost half-spaces preserves convexity for the constrained feasible set as well. It is occupancy mixtures, not generally averages of action probabilities, that yield the averaged returns.</p>
''')

replace(18, 'Make the flow elimination explicit, prove the fractional allocation is globally and uniquely optimal, calculate every dual branch and list the positive occupancy entries for the support count.', ['Solve both state marginals', 'Derive the LP coefficients', 'Prove optimality by an upper bound with equality conditions', 'Expand the dual piecewise slopes', 'Count actual support entries'], r'''
<p><strong>(a) Solve discounted probability flow.</strong> Actions do not alter the deterministic alternation. Write $q_i=\rho(s_i)$. Starting in $s_1$ at $\gamma=1/2$, the flows are $q_1=1/2+(1/2)q_2$ and $q_2=(1/2)q_1$. Substituting gives $q_1=1/2+(1/4)q_1$, so $(3/4)q_1=1/2$ and $q_1=2/3$. Then $q_2=1/3$, and the two masses sum to one. The fast occupancy in $s_i$ is $q_ip_i$, and the slow occupancy is $q_i(1-p_i)$.</p>
<p><strong>(b) Write and solve the LP.</strong> Divide the occupancy-weighted signals by $1-\gamma=1/2$:</p>
<div class="math-block">$$\begin{aligned}
J_r&=2\left(\tfrac23p_1+\tfrac13p_2\right)=\tfrac43p_1+\tfrac23p_2,\\
J_c&=2\left(\tfrac23p_1(1)+\tfrac13p_2(2)\right)=\tfrac43(p_1+p_2).
\end{aligned}$$</div>
<p>The budget $J_c\le1.2=6/5$ becomes $p_1+p_2\le(6/5)(3/4)=9/10$, with $p_1,p_2\in[0,1]$. For every feasible point,</p>
<div class="math-block">$$J_r=\tfrac43(p_1+p_2)-\tfrac23p_2
\le\tfrac43\cdot\tfrac9{10}=\tfrac65.$$</div>
<p>Equality requires both $p_2=0$ and $p_1+p_2=9/10$. The unique optimizer is therefore $p_1=0.9,p_2=0$, with $P^*=J_c=6/5$. The budget buys more reward in $s_1$ because its fast cost is lower; the displayed inequality makes that resource-allocation argument a proof.</p>
<p><strong>(c) Find and verify the dual price.</strong> At a given $\lambda$, fast's penalized one-step rewards are $1-\lambda$ in $s_1$ and $1-2\lambda$ in $s_2$; slow's is zero. Each state's action choice can be maximized separately, giving</p>
<div class="math-block">$$D(\lambda)=\tfrac43\max(0,1-\lambda)
+\tfrac23\max(0,1-2\lambda)+\tfrac65\lambda.$$</div>
<p>On $[0,1/2]$ both fast terms contribute, so $D=2+(-4/3-4/3+6/5)\lambda=2-(22/15)\lambda$. On $[1/2,1]$ only the first contributes, so $D=4/3+(-4/3+6/5)\lambda=4/3-(2/15)\lambda$. For $\lambda\ge1$, both vanish and $D=(6/5)\lambda$.</p>
<p>The first two slopes are negative and the last is positive, so the minimum is at $\lambda^*=1$, where $D(1)=6/5=P^*$. At this price $s_1$ is indifferent between fast and slow, permitting its required mixture, while fast in $s_2$ has reward $1-2=-1\lt0$ and slow is preferred.</p>
<p><strong>(d) Check how much randomization is used.</strong> The optimal action occupancies are</p>
<div class="math-block">$$\rho(s_1,\text{fast})=\tfrac23\tfrac9{10}=\tfrac35,\quad
\rho(s_1,\text{slow})=\tfrac23\tfrac1{10}=\tfrac1{15},\quad
\rho(s_2,\text{fast})=0,\quad\rho(s_2,\text{slow})=\tfrac13.$$</div>
<p>Exactly three entries are positive. There are two visited states and one constraint, so the basic-support bound is $|\mathcal S|+m=3$; the active budget has zero slack. Each state needs one action, leaving one additional action, used only in $s_1$. Thus the policy has one randomization, meeting Altman's bound for $m=1$.</p>
''')

replace(19, 'The matrix/eigenvalue argument is sound but benefits from displayed timing substitutions, a real-versus-integer halving distinction and explicit Jury substitutions. Keep the local inactive-projection scope.', ['Derive the two state equations under the given update timing', 'Compute trace and determinant', 'Use conjugate roots to prove the modulus', 'Calculate nominal period and integer envelope cutoff', 'Substitute all Jury inequalities'], r'''
<p>This is the local linear loop of Section 5, with projections inactive and $K_I\ne0$. The order is important: update $I_k$ using $e_k$, form $\lambda_k$, then produce $e_{k+1}$. Changing that order changes the matrix.</p>
<p><strong>(a) Shift the integral state to its equilibrium.</strong> Since $\delta_{k-1}=I_{k-1}-\lambda^*/K_I$ and $I_k=I_{k-1}+e_k$,</p>
<div class="math-block">$$\begin{aligned}
\lambda_k-\lambda^*
&=K_Pe_k+K_I\left(\delta_{k-1}+\frac{\lambda^*}{K_I}+e_k\right)-\lambda^*\\
&=(K_P+K_I)e_k+K_I\delta_{k-1},\\
e_{k+1}&=\big(1-c(K_P+K_I)\big)e_k-cK_I\delta_{k-1},\\
\delta_k&=\delta_{k-1}+e_k.
\end{aligned}$$</div>
<p>Thus for $x_k=(e_k,\delta_{k-1})^\top$,</p>
<div class="math-block">$$M=\begin{pmatrix}1-c(K_P+K_I)&-cK_I\\1&1\end{pmatrix},\quad
t=\operatorname{tr}M=2-c(K_P+K_I),\quad
q=\det M=1-c(K_P+K_I)+cK_I=1-cK_P.$$</div>
<p><strong>(b) Integral action alone preserves the mode envelope.</strong> The eigenvalues solve $z^2-tz+q=0$. When $K_P=0$, $q=1$ and $t=2-cK_I$. For $0\lt cK_I\lt4$, we have $-2\lt t\lt2$, so the discriminant $t^2-4$ is negative. The two roots are a conjugate pair; their product is $z\bar z=q=1$, hence $|z|=1$. Write $z=e^{\pm i\vartheta}$: their sum gives $2\cos\vartheta=t$, so $\cos\vartheta=1-cK_I/2$.</p>
<p>For $c=0.4,K_I=0.1$, this is $\cos\vartheta=1-0.04/2=0.98$. Thus $\vartheta=\arccos(0.98)\approx0.200335$ radians per iteration, and the nominal oscillation period is $2\pi/\vartheta\approx31.36$ iterations, about $31$. A nonzero rotating mode neither grows nor decays; this nominal period need not imply exact repetition after an integer number of steps.</p>
<p><strong>(c) Check damping before using the complex-pair formula.</strong> For a complex conjugate pair, $|z|^2=z\bar z=q=1-cK_P$, so the modulus is $r=\sqrt{1-cK_P}$. At $c=0.4,K_I=0.1,K_P=0.5$,</p>
<div class="math-block">$$t=2-0.4(0.5+0.1)=1.76,\qquad
q=1-0.4(0.5)=0.8,\qquad
t^2-4q=3.0976-3.2=-0.1024\lt0.$$</div>
<p>The roots really are complex, and $r=\sqrt{0.8}\approx0.894427\lt1$. Their envelope is multiplied by $r$ per iteration. Solve $r^n\le1/2$: taking logs and dividing by $\ln r\lt0$ gives $n\ge\ln2/\ln(1/r)\approx6.21257$. The continuous halving estimate is about $6.2$ iterations; the first whole-number budget is $7$, since $r^6=0.512\gt0.5$ and $r^7\approx0.457947\lt0.5$.</p>
<p><strong>(d) Use strict stability conditions, including real roots.</strong> For $z^2-tz+q$, Jury's conditions are $1-q\gt0$, $1-t+q\gt0$ and $1+t+q\gt0$. Substituting the values from (a) gives</p>
<div class="math-block">$$cK_P\gt0,\qquad cK_I\gt0,\qquad
4-c(2K_P+K_I)\gt0.$$</div>
<p>These imply $cK_P\lt2$, so an equivalent region is $0\lt cK_P\lt2$, $cK_I\gt0$, $c(2K_P+K_I)\lt4$. Equalities are stability boundaries, not asymptotic stability. The complex-root modulus shortcut is insufficient outside its discriminant condition.</p>
<p>Here $c=\eta b^2$ includes the policy learning rate and cost sensitivity. Doubling $\eta$ has the same loop-gain effect as doubling both controller gains; scaling cost and budget by $\kappa\gt0$ scales $b$ by $\kappa$ and $c$ by $\kappa^2$. With the curvature factor $a$ of Section 5(c), $t=1+a-c(K_P+K_I)$ and $q=a-cK_P$; the same three substitutions give $a-1\lt cK_P\lt a+1$, $cK_I\gt0$, $c(2K_P+K_I)\lt2(1+a)$. These are local linear conclusions, with no unconditional claim about clipped noisy nonlinear training.</p>
''')

replace(20, 'Make atom splitting and the global minimum of the tail objective explicit, then calculate the Gaussian fit from both moments and distinguish its own exact-law tail value from the discrete policy tail.', ['Show mean and quantile CDF values', 'Split the worst five percent at the quantile atom', 'Compute each candidate and every linear-region slope', 'Calculate mean, variance, Gaussian density factor and estimate', 'Compare the two tail-budget conclusions'], r'''
<p><strong>(a) Compute the mean, quantile and tail separately.</strong> The mean is $0.9(0)+0.08(10)+0.02(100)=0.8+2=2.8$. The CDF is $0.9$ at $0$ and $0.98$ at $10$, so the first value reaching $0.95$ is $\mathrm{VaR}_{0.95}=10$.</p>
<p>The worst $5\%$ first contains all the $2\%$ mass at cost $100$. The remaining $3\%$ is taken from the $8\%$ mass at cost $10$. Dividing its weighted cost by its mass gives</p>
<div class="math-block">$$\mathrm{CVaR}_{0.95}(Z)
=\frac{0.02(100)+0.03(10)}{0.05}
=\frac{2+0.3}{0.05}=46.$$</div>
<p>Taking only part of the quantile atom is required. Conditioning on every outcome with $Z\ge10$ would select $10\%$ of the distribution, not the requested worst $5\%$.</p>
<p><strong>(b) Verify by minimizing the tail objective.</strong> With $1/(1-0.95)=20$, put $H(\nu)=\nu+20\mathbb E[(Z-\nu)_+]$. At the three candidate atoms,</p>
<div class="math-block">$$\begin{aligned}
H(0)&=0+20\big(0.08(10)+0.02(100)\big)=56,\\
H(10)&=10+20\big(0.02(100-10)\big)=10+36=46,\\
H(100)&=100+20(0)=100.
\end{aligned}$$</div>
<p>To check the global minimum, not only three trial values, expand on every region between atoms:</p>
<div class="math-block">$$H(\nu)=\begin{cases}
56-19\nu,&\nu\le0,\\
56-\nu,&0\le\nu\le10,\\
40+0.6\nu,&10\le\nu\le100,\\
\nu,&\nu\ge100.
\end{cases}$$</div>
<p>For example, on $[0,10]$ the excess mean is $0.08(10-\nu)+0.02(100-\nu)=2.8-0.1\nu$; on $[10,100]$ only the $100$ atom contributes, giving $0.02(100-\nu)$. The slopes are $-19,-1,0.6,1$, so $H$ decreases up to $10$ and increases afterwards. Its minimum is exactly $46$ at $\nu=10$.</p>
<p><strong>(c) Fit and evaluate the Gaussian law.</strong> The second moment is $0.08(10^2)+0.02(100^2)=8+200=208$. Thus $\sigma^2=208-2.8^2=208-7.84=200.16$ and $\sigma=\sqrt{200.16}\approx14.147791$.</p>
<p>For the fitted Gaussian, the upper-tail fraction is $0.05$. Let $q=\Phi^{-1}(0.95)\approx1.644854$. Symmetry gives $\Phi^{-1}(0.05)=-q$, and the density is even, so $\varphi(\Phi^{-1}(0.05))=\varphi(q)\approx0.103136$. Using the given Gaussian tail formula yields</p>
<div class="math-block">$$\mu+\frac{\sigma\varphi(q)}{0.05}
=2.8+\frac{\sqrt{200.16}\,\varphi(\Phi^{-1}(0.95))}{0.05}
\approx31.982830,$$</div>
<p>which is strictly between $31.982$ and $31.984$, and rounds to about $32$. This expression is the true CVaR of the fitted Gaussian distribution; it is not the true CVaR of the original discrete cost. The original is $46$, so the fit underestimates it by $(46-31.982830)/46\approx30.47\%$.</p>
<p>A tail budget of $32$ would pass the fitted Gaussian check but fail the actual discrete policy's tail value $46$. Matching two moments does not preserve the large tail atom. Richer distributional models or sample-based tail estimation can represent more than mean and variance, but their modelling and estimation errors still require checks. Decimal displays here approximate the exact-law expressions.</p>
''')

# Keep the unusually complete existing monitoring proof. Add only the worked
# instance needed to make its already-qualified concrete rollout claim inspectable.
original_monitoring = baseline['exercises'][20]['solution']['html']
marker = 'This directly verified instance does not require an unbiased-epoch assumption.'
assert original_monitoring.count(marker) == 1
trace_html = r'''
<p><strong>Work through that particular execution.</strong> With one step per epoch and step size $1$, use the current state and multipliers to choose the stated maximizing mode, then update</p>
<div class="math-block">$$\lambda_{i,k+1}=\left[\lambda_{i,k}+\frac13-\mathbf 1\{s_k=R_i\}\right]_+,
\qquad i=1,2.$$</div>
<p>A visit to region $i$ subtracts $2/3$ from its price; being elsewhere adds $1/3$, with projection at zero. The complete prefix and first cycle are:</p>
<table><thead><tr><th>$k$</th><th>$s_k$</th><th>$(\lambda_{1,k},\lambda_{2,k})$</th><th>$s_{k+1}$</th><th>Next multipliers</th></tr></thead><tbody>
<tr><td>$0$</td><td>$R_0$</td><td>$(0,0)$</td><td>$R_1$</td><td>$(1/3,1/3)$</td></tr>
<tr><td>$1$</td><td>$R_1$</td><td>$(1/3,1/3)$</td><td>$R_0$</td><td>$(0,2/3)$</td></tr>
<tr><td>$2$</td><td>$R_0$</td><td>$(0,2/3)$</td><td>$R_2$</td><td>$(1/3,1)$</td></tr>
<tr><td>$3$</td><td>$R_2$</td><td>$(1/3,1)$</td><td>$R_0$</td><td>$(2/3,1/3)$</td></tr>
<tr><td>$4$</td><td>$R_0$</td><td>$(2/3,1/3)$</td><td>$R_1$</td><td>$(1,2/3)$</td></tr>
<tr><td>$5$</td><td>$R_1$</td><td>$(1,2/3)$</td><td>$R_0$</td><td>$(1/3,1)$</td></tr>
<tr><td>$6$</td><td>$R_0$</td><td>$(1/3,1)$</td><td>$R_2$</td><td>$(2/3,4/3)$</td></tr>
<tr><td>$7$</td><td>$R_2$</td><td>$(2/3,4/3)$</td><td>$R_2$</td><td>$(1,2/3)$</td></tr>
<tr><td>$8$</td><td>$R_2$</td><td>$(1,2/3)$</td><td>$R_0$</td><td>$(4/3,0)$</td></tr>
<tr><td>$9$</td><td>$R_0$</td><td>$(4/3,0)$</td><td>$R_1$</td><td>$(5/3,1/3)$</td></tr>
<tr><td>$10$</td><td>$R_1$</td><td>$(5/3,1/3)$</td><td>$R_1$</td><td>$(1,2/3)$</td></tr>
</tbody></table>
<p>For example, at $k=5$ the current region's price is exactly the threshold $1$, so the prescribed selector returns; its update is $[1-2/3]_+=1/3$, while the other price becomes $2/3+1/3=1$. At $k=7$, region $R_2$ has price $4/3\gt1$ above its rival $2/3$, so the selector stays. At $k=11$ the augmented state is again $(R_1,1,2/3)$, exactly its value at $k=5$. Because the next state and update are deterministic functions of the augmented state, the six rows $5$ through $10$ then repeat forever.</p>
<p>Each cycle contains two visits to each physical state. Any initial prefix and unfinished cycle have a bounded number of visits, so their contribution divided by horizon $T$ tends to zero. The three realized visit fractions therefore tend to $2/6=1/3$. This is a direct calculation for this specified selector, step and start; it is not an appeal to unbiased epoch estimates.</p>
'''
# Insert outside the original paragraph, preserving its surrounding proof prose.
monitoring = original_monitoring.replace(marker, '</p>'+trace_html+'<p>'+marker)
replace(21, 'Retain the full existing achievable-polytope, face-classification, state-only representation and theorem-scope reasoning. Supplement its concrete execution claim with the actual prefix/cycle and row-level accounting.', ['Add the exact per-step projected utility update', 'Show every prefix and cycle state/multiplier pair', 'Explain threshold and high-price action cases', 'Prove periodicity and limiting visit fractions from the table', 'Retain the distinction between this instance and the conditional general theorem'], monitoring)

RETAIN = {
    4: 'The geometric factor is used for both constant signals, both totals are evaluated, feasibility is checked against the actual cumulative budget and the per-step-versus-return distinction is explained.',
    5: 'Both action occupancies, the weighted one-step reward/cost calculations, their discount normalisation and the probability-mass check are explicit.',
    6: 'The two signed residuals are evaluated before the penalty; each Lagrangian value is computed and its meaning is separated from the dual optimization.',
    7: 'Both sequential updates substitute the preceding multiplier and the respective cost, including the negative unprojected second value and projection to zero.',
    8: 'Each state occupancy is computed from its visit times, both flow equations are checked with incoming mass, and the occupancy-based return is verified against the direct geometric tail.',
    9: 'The one-step affine quantities and discounted totals are supplied, the full probability/budget intersection is solved, and monotonicity selects and evaluates the endpoint optimum while comparing both pure actions.',
    10: 'The mean, CDF threshold and tail average are each calculated, with the necessary fractional quantile-atom interpretation explicitly stated.',
    11: 'Both current-time remaining-budget updates and the original-time spend/remainder are computed and cross-checked; the unchanged numeric budget does not get mistaken for replenishment.',
    13: 'Both orders of applying the positive part are evaluated, and the positive first residual is the explicit counterexample to per-iterate feasibility under zero signed-average violation.',
    14: 'The rare-failure probability, expected-budget equality, quantile CDF and fractional five-percent CVaR calculation are all explicit and their different meanings are explained.',
    17: 'The answer supplies the full affine-mixture inequality proving convexity, both feasible-policy weak-duality signs, the min-convention concavity inequality and dual direction, and the exact kinked walkthrough dual. Every requested proof and convention comparison is present.',
}
assert len(replacements)==10 and len(RETAIN)==11
assert not set(replacements)&set(RETAIN)
assert set(replacements)|set(RETAIN)==set(range(1,22))
assert not (ROOT/OUT).exists() and not (ROOT/ARITHMETIC).exists()
assert ref(baseline['source']['file'])['sha256']==baseline['source']['sha256']

checks=[]
def record(name,actual,expected=None,exact=True):
    if expected is not None:assert actual==expected,name
    checks.append({'name':name,'actual':str(actual),'expected':str(expected) if expected is not None else None,'exact_rational':exact})
record('B1 optimal p',(F(65,100)-F(1,5))/F(9,5),F(1,4))
record('B1 reward',20+30*F(1,4),F(55,2))
record('B1 price',F(30)/F(9,5),F(50,3))
record('B2 new p',(1-F(2,5))/F(18,5),F(1,6))
record('B2 optimal reward',40+60*F(1,6),F(50))
record('B2 reused-p cost',F(2,5)+F(18,5)*F(4,9),F(2))
record('B3 new remaining budget',(F(14,27)-F(1,2))/F(9,10),F(5,243))
record('B3 original-time remainder',F(9,10)**3*F(5,243),F(15,1000))
record('B3 spend',F(2,5)+F(9,10)*F(1,5)+F(9,10)**2*F(1,2),F(985,1000))
record('P9 dual optimum value',2+F(3,2),F(7,2))
record('8.3 state marginals',(F(2,3),F(1,3)),(F(2,3),F(1,3)))
record('8.3 optimum reward',F(4,3)*F(9,10),F(6,5))
record('8.3 first dual slope',-F(4,3)-F(4,3)+F(6,5),-F(22,15))
record('8.3 second dual slope',-F(4,3)+F(6,5),-F(2,15))
theta=math.acos(.98);r=math.sqrt(.8)
record('8.4 eigenvalue angle',theta,exact=False)
record('8.4 nominal period',2*math.pi/theta,exact=False)
record('8.4 discriminant',F(176,100)**2-4*F(8,10),-F(1024,10000))
record('8.4 real halving budget',math.log(2)/math.log(1/r),exact=False)
assert r**6>.5>r**7
record('8.4 first whole halving budget',7,7)
mean=F(8,100)*10+F(2,100)*100
record('8.5 mean',mean,F(14,5))
record('8.5 tail average',(F(2,100)*100+F(3,100)*10)/F(5,100),F(46))
variance=F(208)-mean**2
record('8.5 variance',variance,F(5004,25))
q=NormalDist().inv_cdf(.95);density=math.exp(-q*q/2)/math.sqrt(2*math.pi)
gaussian=float(mean)+math.sqrt(float(variance))*density/.05
assert 31.982<gaussian<31.984 and gaussian<32<46
record('8.5 exact-law normal quantile float',q,exact=False)
record('8.5 gaussian std float',math.sqrt(float(variance)),exact=False)
record('8.5 gaussian density float',density,exact=False)
record('8.5 gaussian CVaR float',gaussian,exact=False)

state=0;prices=[F(0),F(0)];seen={};trace=[]
for k in range(30):
    augmented=(state,*prices)
    if augmented in seen:
        start=seen[augmented];period=k-start;break
    seen[augmented]=k
    if state==0:next_state=1 if prices[0]>=prices[1] else 2
    else:
        i=state-1;j=1-i
        next_state=state if prices[i]>1 and prices[i]>=prices[j] else 0
    next_prices=[max(F(0),prices[i]+F(1,3)-(1 if state==i+1 else 0)) for i in range(2)]
    trace.append({'k':k,'state':state,'prices':list(map(str,prices)),'next_state':next_state,'next_prices':list(map(str,next_prices))})
    state=next_state;prices=next_prices
assert start==5 and period==6 and k==11
assert Counter(x['state'] for x in trace[start:])=={0:2,1:2,2:2}
record('8.6 exact cycle start',start,5)
record('8.6 exact cycle period',period,6)
arithmetic={'status':'passed_author_arithmetic_and_exact_rational_recomputations','page':'cmdp.html','author':'/root/review_gaussian35',
            'created_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref('book/solutions/drafts/build-cmdp-thorough-v1.py'),
            'checks':checks,'monitoring_actual_fraction_trace':trace,
            'native_monitoring_reference':ref('verification/lean/SafeLearning/CompleteMonitoringDeterministicPath23.lean'),
            'limits':'Native Fraction/NormalDist author calculations and source correspondence only; no new compiler success, independent review or formal promotion is claimed.'}
(ROOT/ARITHMETIC).write_text(json.dumps(arithmetic,ensure_ascii=False,indent=2)+'\n')
rows=[]
for b in baseline['exercises']:
    n=b['ordinal'];decision='replace' if n in replacements else 'retain';body=replacements.get(n,b['solution']['html'])
    rows.append({'inventory_key':b['inventory_key'],'source_file':b['source_file'],'authoring_file':b['authoring_file'],
                 'ordinal':n,'anchor':b['anchor'],'label':b['label'],
                 'original_source_sha256':b['source_sha256'],'original_authoring_source_sha256':b['authoring']['source_sha256'],
                 'original_question_sha256':b['problem']['sha256'],'original_hint_sha256':[h['disclosure']['sha256'] for h in b['hints']],
                 'original_solution_sha256':b['solution']['sha256'],'decision':decision,'replacement_html':body,
                 'replacement_sha256':sha256(body.encode()).hexdigest(),
                 'thoroughness_rationale':rationales[n] if decision=='replace' else RETAIN[n],
                 'specific_improvements':improvements.get(n,[]),'whole_question_hint_answer_and_background_read':True,
                 'pedagogical_status':'authored_pending_independent_review','question_hint_disclosure_notation_anchor_preservation_required':True})
draft={'schema':'individual_solution_draft_v1','status':'authored_pending_independent_review','author':'/root/review_gaussian35',
       'created_at_utc':datetime.now(timezone.utc).isoformat(),'page':'cmdp.html',
       'audience':'First-course linear algebra and single-variable calculus; explain additional CMDP, probability, duality and risk concepts locally.',
       'baseline':ref(BASELINE),'baseline_manifest':ref('book/solutions/baseline-source90/manifest.json'),'inventory':baseline['inventory'],
       'page_contract':ref('page_contract.md'),'page_contract_fully_read':True,'criteria':ref('book/solutions/README.md'),
       'source_refs':[ref('SafeLearning/cmdp.html'),ref('book/chapters/cmdp.html')],
       'context_read':['Full canonical teaching text for all8 sections, assumptions, definitions, examples, counterexamples, corrections, algorithms and application context',
                       'Entire dual-ascent interactive derivation data and controller-model/timing qualifications',
                       'Full authored application source and all21 questions, hints and original solutions'],
       'counts':{'reviewed_exercises':21,'replace':10,'retain':11,'book_lab_exercises':3},'exercises':rows,
       'arithmetic_report':ref(ARITHMETIC),'new_external_citations':[],'independent_pedagogical_approval_claimed':False,
       'rendered_qa_claimed':False,'whole_page_reserialized':False,'canonical_source_owner_selection_progress_publication_mutations':False,
       'scope':'Exact solution-body decisions only. Retain all original questions, hints, disclosures, anchors, scripts, hooks, notation and qualified Source90 facts. Mirror lab replacements to their authored source in candidates. Root arranges independent review, QA and integration.',
       'helper':ref('book/solutions/drafts/build-cmdp-thorough-v1.py')}
(ROOT/OUT).write_text(json.dumps(draft,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'draft':ref(OUT),'arithmetic':ref(ARITHMETIC),'counts':draft['counts']},ensure_ascii=False))
