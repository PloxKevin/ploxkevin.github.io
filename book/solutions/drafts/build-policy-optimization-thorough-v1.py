"""Author twenty-one exact solution decisions; no source or coverage mutations."""
from datetime import datetime, timezone
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json
import math

ROOT=Path(__file__).resolve().parents[3]
BASELINE='book/solutions/baseline-source90/pages/policy-optimization.html.json'
OUT='book/solutions/drafts/policy-optimization-thorough-solutions-v1.json'
ARITHMETIC='reports/solution-review/policy-optimization-author-arithmetic-v1.json'


def ref(file):
    return {'file':file,'sha256':sha256((ROOT/file).read_bytes()).hexdigest()}


replacements={};rationales={};improvements={}
def replace(n,why,specific,html):
    assert n not in replacements
    replacements[n]='\n'+html.strip()+'\n';rationales[n]=why;improvements[n]=specific


replace(1,'The original comparison is correct but compresses four different calculations into a list of results. Compute each using its own metric and state the linearized-feasibility scope.', ['Calculate both Euclidean lengths','Expand each quadratic trust cost','Evaluate the reward dot products','Check both cost residuals separately'],r'''
<p>Use the original local model $g=(2,1)$, $H=\operatorname{diag}(1,4)$, trust budget $\delta=1/2$ and cost residual $-1/5+v_1$. All components of $v$ are dimensionless parameter changes, not temperatures or actuator commands.</p>
<p><strong>Euclidean size.</strong> Both candidates have length $1/2$: $\|s\|_2=\sqrt{(1/2)^2+0^2}=1/2$ and $\|t\|_2=\sqrt{0^2+(1/2)^2}=1/2$.</p>
<p><strong>Quadratic trust cost.</strong> The matrix weights the second direction four times as much:</p>
<div class="math-block">$$\tfrac12s^\top Hs=\tfrac12\big((1/2)^2+4(0)^2\big)=\tfrac18,\qquad
\tfrac12t^\top Ht=\tfrac12\big(0^2+4(1/2)^2\big)=\tfrac12.$$</div>
<p>Both satisfy the trust budget, but $s$ is strictly inside its ellipse and $t$ lies on its boundary.</p>
<p><strong>Reward prediction.</strong> The linear improvements are $g^\top s=2(1/2)+1(0)=1$ and $g^\top t=2(0)+1(1/2)=1/2$.</p>
<p><strong>Local cost feasibility.</strong> For $s$, the residual is $-1/5+1/2=3/10\gt0$, so it fails. For $t$, the residual is $-1/5+0=-1/5\le0$, so it passes. Thus the apparently cheap, high-reward direction is not admissible for this local subproblem.</p>
<p>Euclidean length, the trust matrix and the cost gradient answer three different questions. Equal parameter distance does not imply equal predicted distribution change or equal safety-surrogate feasibility. These are exact comparisons within the given local model; a true controller constraint still needs its own verification.</p>
''')

replace(2,'Write the stationarity vector and both active residuals before solving the multipliers, then explain the two resource prices within this local convex problem.', ['Differentiate the stated maximization Lagrangian','Substitute the optimizer and solve both coordinates','Verify nonnegativity and complementary slackness','Limit the price interpretation to the local model'],r'''
<p>The original step is $s^*=(1/5,\sqrt6/5)$. With the stated maximization Lagrangian, differentiating with respect to $s$ gives the stationarity condition</p>
<div class="math-block">$$g-\lambda Hs^*-\nu b=0,\qquad
Hs^*=\begin{pmatrix}1/5\\4\sqrt6/5\end{pmatrix},\qquad b=\begin{pmatrix}1\\0\end{pmatrix}.$$</div>
<p>The second coordinate contains no cost multiplier, so it first determines $\lambda$:</p>
<div class="math-block">$$1=\lambda\frac{4\sqrt6}{5}
\quad\Longrightarrow\quad\lambda=\frac5{4\sqrt6}\gt0.$$</div>
<p>The first coordinate is then $2=\lambda/5+\nu$. Since $\lambda/5=1/(4\sqrt6)$, it gives $\nu=2-1/(4\sqrt6)\gt0$. Positivity follows, for example, from $\sqrt6\gt1$, which makes the subtracted term less than $1/4$.</p>
<p><strong>Check the two complementarity products.</strong> The trust residual is</p>
<div class="math-block">$$\tfrac12(s^*)^\top Hs^*-\tfrac12
=\tfrac12\left(\frac1{25}+4\frac6{25}\right)-\tfrac12=0.$$</div>
<p>The cost residual is $s_1^*-1/5=0$. Therefore $\lambda(\tfrac12(s^*)^\top Hs^*-1/2)=0$ and $\nu(s_1^*-1/5)=0$, as required. The step is feasible and both multipliers are nonnegative.</p>
<p>In this local convex optimization, $\lambda$ prices an extra unit of quadratic trust budget and $\nu$ prices an extra unit in the right side of the cost half-space. Stationarity balances the reward gradient against these two resource gradients. They describe marginal trade-offs in this subproblem; they do not include gradient-estimation error, the nonlinear constraint remainder or a separate claim that the physical controller is safe.</p>
''')

replace(3,'Show the squared norms and signed upper bounds explicitly, then distinguish the logical force of a bound from the case in which it is the true constraint identity.', ['Compute the norm of each optimizer','Substitute every term in the remainder bound','Explain sufficient certification and inconclusive failure','Handle the equality-to-bound case'],r'''
<p>Let $U(s)=-1/5+s_1+(1/5)(s_1^2+s_2^2)$, and keep the stated hypothesis that the true residual satisfies $C(s)-d\le U(s)$ throughout the relevant trust region. A value $U(s)\le0$ is therefore sufficient for true feasibility.</p>
<p><strong>Original optimizer.</strong> At $s^*=(1/5,\sqrt6/5)$, the squared norm is $(1/5)^2+(\sqrt6/5)^2=1/25+6/25=7/25$. Thus</p>
<div class="math-block">$$U(s^*)=-\frac15+\frac15+\frac15\frac7{25}=\frac7{125}\gt0.$$</div>
<p>This upper bound cannot certify feasibility of the original step. It does not show that the true residual is positive: a true value below the upper bound may still be nonpositive.</p>
<p><strong>Conservative optimizer.</strong> At $s=(0,1/2)$, the squared norm is $1/4$, giving</p>
<div class="math-block">$$U(0,1/2)=-\frac15+0+\frac15\frac14
=-\frac15+\frac1{20}=-\frac3{20}\lt0.$$</div>
<p>The true residual is at most this negative number, so this step is feasible with margin at least $3/20$ under the assumed valid bound.</p>
<p>If the true residual equals $U$ exactly, the first test is no longer inconclusive: the original optimizer truly violates the constraint by $7/125$. The conservative optimizer's true margin is then exactly $3/20$. An upper-bound inequality and an exact model identity give different information on a failed test.</p>
''')

replace(16,'The general proof is already correct; display its vector algebra and fully solve the numerical Bellman/occupancy example so the stated values do not appear as an unexplained inverse product.', ['Derive the averaged advantage vector','Show the inverse relation and normalization factor','Solve both old and new two-state values','Evaluate all Q values and occupancies','Prove exactness of the constant-advantage surrogate'],r'''
<p>Use the finite discounted setting of this section, with bounded rewards, $0\lt\gamma\lt1$, a common initial law $\mu$, and the row-stochastic convention specified in the question.</p>
<p><strong>(a) Average the old action-values under the new policy.</strong> The Bellman action-value identity gives</p>
<div class="math-block">$$\begin{aligned}
\bar a(s)&=\sum_a\pi'(a\mid s)\big(Q^\pi(s,a)-V^\pi(s)\big)\\
&=\sum_a\pi'(a\mid s)\left(r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V^\pi(s')\right)-V^\pi(s)\\
&=r_{\pi'}(s)+\gamma(P_{\pi'}V^\pi)(s)-V^\pi(s).
\end{aligned}$$</div>
<p>The state value is subtracted once because $\sum_a\pi'(a\mid s)=1$. In vector form, $\bar a=r_{\pi'}+\gamma P_{\pi'}V^\pi-V^\pi$.</p>
<p><strong>(b) Solve for the value difference.</strong> Starting from $V^{\pi'}=r_{\pi'}+\gamma P_{\pi'}V^{\pi'}$, insert and subtract $\gamma P_{\pi'}V^\pi$:</p>
<div class="math-block">$$\begin{aligned}
V^{\pi'}-V^\pi
&=\big(r_{\pi'}+\gamma P_{\pi'}V^\pi-V^\pi\big)
 +\gamma P_{\pi'}(V^{\pi'}-V^\pi)\\
&=\bar a+\gamma P_{\pi'}(V^{\pi'}-V^\pi),\\
(I-\gamma P_{\pi'})(V^{\pi'}-V^\pi)&=\bar a.
\end{aligned}$$</div>
<p>A row-stochastic matrix has induced infinity-norm one, so the Neumann series $\sum_{t\ge0}\gamma^tP_{\pi'}^t$ converges and is the inverse of $I-\gamma P_{\pi'}$. Multiplication gives $V^{\pi'}-V^\pi=(I-\gamma P_{\pi'})^{-1}\bar a$. Average over the common initial law:</p>
<div class="math-block">$$\begin{aligned}
J(\pi')-J(\pi)
&=\mu^\top\sum_{t=0}^{\infty}\gamma^tP_{\pi'}^t\bar a\\
&=\frac1{1-\gamma}(d^{\pi'})^\top\bar a
=\frac1{1-\gamma}\sum_sd^{\pi'}(s)\sum_a\pi'(a\mid s)A^\pi(s,a).
\end{aligned}$$</div>
<p>Here $\mu^\top P_{\pi'}^t$ is the time-$t$ state law, and multiplying its discounted sum by $1-\gamma$ defines the normalized occupancy. This is why the performance-difference lemma contains the reciprocal factor.</p>
<p><strong>(c) Work the two-state example.</strong> Under $\pi$, the next state is equally likely to be $0$ or $1$ from either state. Write $m=(V^\pi(0)+V^\pi(1))/2$. The Bellman equations are $V^\pi(0)=0+(1/2)m$ and $V^\pi(1)=1+(1/2)m$. Averaging them gives $m=1/2+(1/2)m$, so $m=1$ and $V^\pi=(1/2,3/2)$. The start in state $0$ gives $J(\pi)=1/2$.</p>
<p>In action order (stay, switch), evaluate all four old-policy action-values:</p>
<div class="math-block">$$\begin{aligned}
Q^\pi(0,\text{stay})&=0+\tfrac12\tfrac12=\tfrac14,&
Q^\pi(0,\text{switch})&=0+\tfrac12\tfrac32=\tfrac34,\\
Q^\pi(1,\text{stay})&=1+\tfrac12\tfrac32=\tfrac74,&
Q^\pi(1,\text{switch})&=1+\tfrac12\tfrac12=\tfrac54.
\end{aligned}$$</div>
<p>Subtracting the respective values gives $A^\pi(0,\cdot)=(-1/4,1/4)$ and $A^\pi(1,\cdot)=(1/4,-1/4)$. Policy $\pi'$ switches from $0$ and stays in $1$, choosing the positive advantage in both states, so $\bar a=(1/4,1/4)$.</p>
<p>Under $\pi'$, the value at state $1$ solves $V^{\pi'}(1)=1+(1/2)V^{\pi'}(1)$, giving $2$. From state $0$ it is $0+(1/2)(2)=1$. Thus $V^{\pi'}=(1,2)$ and $J(\pi')-J(\pi)=1-1/2=1/2$.</p>
<p>The new trajectory visits $0$ only initially, then $1$ forever. Hence $d^{\pi'}(0)=1/2$ and $d^{\pi'}(1)=(1/2)\sum_{t\ge1}(1/2)^t=1/2$. The lemma gives $2((1/2)(1/4)+(1/2)(1/4))=1/2$, the direct difference. At the vector level, $P_{\pi'}=\begin{pmatrix}0&1\\0&1\end{pmatrix}$ and $(I-\tfrac12P_{\pi'})^{-1}=\begin{pmatrix}1&1\\0&2\end{pmatrix}$; applying it to $\bar a$ gives $(1/2,1/2)=V^{\pi'}-V^\pi$.</p>
<p>For the old policy, time zero is in $0$, while every later state law is uniform. Therefore $d^\pi(0)=(1/2)(1+(1/2)\sum_{t\ge1}(1/2)^t)=3/4$ and $d^\pi(1)=1/4$. The old-distribution surrogate is also $L_\pi(\pi')=2((3/4)(1/4)+(1/4)(1/4))=1/2$.</p>
<p>This exactness is special: the averaged advantage is the same constant at both states. Its distribution-shift error is $2\sum_s(d^{\pi'}-d^\pi)(s)(1/4)=0$, because the two probability laws both sum to one. A changed state distribution usually does matter when the averaged advantages vary across states.</p>
''')

replace(17,'Expand the dual substitution, prove joint convexity directly from its supremum of affine functions, and carry the numerical example through exact inner products, regime tests, multipliers and unrounded primal/dual checks.', ['Complete the square for the dual','Use a direct convexity proof','Certify the feasible TRPO case by weak duality equality','Show every exact q/r/s and reduced-dual coefficient','Compute both dual candidates','Verify both constraints and objective with exact radicals'],r'''
<p><strong>(a) Maximize the Lagrangian in $x$.</strong> Let $w=g-\nu b$. For $\lambda\gt0$, $H\succ0$ makes</p>
<div class="math-block">$$\mathcal L=w^\top x-\frac\lambda2x^\top Hx-\nu c+\lambda\delta$$</div>
<p>strictly concave in $x$. Its stationary equation is $w-\lambda Hx=0$, giving $x(\lambda,\nu)=H^{-1}w/\lambda$. To see the maximum value, complete the square:</p>
<div class="math-block">$$w^\top x-\frac\lambda2x^\top Hx
=\frac{w^\top H^{-1}w}{2\lambda}
-\frac\lambda2\left(x-\frac{H^{-1}w}{\lambda}\right)^\top
 H\left(x-\frac{H^{-1}w}{\lambda}\right).$$</div>
<p>The final quadratic is nonnegative and vanishes at the stationary point. Expanding $w^\top H^{-1}w=q-2\nu r+\nu^2s$ gives</p>
<div class="math-block">$$D(\lambda,\nu)=\frac{q-2\nu r+\nu^2s}{2\lambda}-\nu c+\lambda\delta.$$</div>
<p>For joint convexity, hold $x$ fixed: $\mathcal L(x,\lambda,\nu)$ is affine in $(\lambda,\nu)$. For two multiplier pairs and weight $\kappa\in[0,1]$, the maximum of their weighted sum is at most the weighted sum of their maxima. Thus $D$ satisfies the convexity inequality on $\lambda\gt0,\nu\ge0$. This proof does not require convexity of the original policy parametrization.</p>
<p><strong>(b) Certify the TRPO case.</strong> The unconstrained trust-region optimizer is $x_0=\sqrt{2\delta/q}\,H^{-1}g$. For every point in the ellipsoid, Cauchy&ndash;Schwarz in the $H$ metric gives $g^\top x\le\sqrt{q}\sqrt{x^\top Hx}\le\sqrt{2\delta q}$, attained at $x_0$. The hypothesis says precisely that $c+b^\top x_0=c+r\sqrt{2\delta/q}\le0$, so this ellipsoid optimizer is also feasible for CPO.</p>
<p>Choose $\lambda_0=\sqrt{q/(2\delta)}$ and $\nu=0$. Substitution gives $D(\lambda_0,0)=q/(2\lambda_0)+\lambda_0\delta=\sqrt{2\delta q}=g^\top x_0$. Every dual value is an upper bound on each feasible objective, since subtracting nonpositive constraint residuals with nonnegative multipliers can only raise it. Therefore no multiplier pair can have a dual value below this attained primal value: $(\lambda_0,0)$ is a global dual minimizer and CPO returns $x_0$. Equivalently, $\partial_\lambda D=0$ there and $\partial_\nu D=-(\lambda_0c+r)/\lambda_0\ge0$, the correct derivative sign at the boundary $\nu=0$.</p>
<p><strong>(c) Compute the given example using exact inverse vectors.</strong> Here $g=(1,2/5)$, $b=(3/5,4/5)$, $c=-1/10$ and $\delta=1/20$. The supplied vectors give</p>
<div class="math-block">$$\begin{aligned}
q&=1\frac{16}{35}+\frac25\frac6{35}=\frac{80+12}{175}=\frac{92}{175},\\
r&=1\frac4{35}+\frac25\frac{26}{35}=\frac{20+52}{175}=\frac{72}{175},\\
s&=\frac35\frac4{35}+\frac45\frac{26}{35}=\frac{12+104}{175}=\frac{116}{175}.
\end{aligned}$$</div>
<p>The hyperplane distance test is $c^2/s=(1/100)(175/116)=7/464\approx0.015086\lt2\delta=0.1$, so it cuts the ellipsoid. The TRPO constraint residual is $c+r\sqrt{2\delta/q}\approx0.079440\gt0$, so that step fails and the cost price must be active.</p>
<p>Minimizing the dual over $\nu\ge0$ gives $\nu(\lambda)=[(\lambda c+r)/s]_+$. Its positive-price region is $0\lt\lambda\lt r/|c|=144/35$. On that region, the reduced dual has coefficients</p>
<div class="math-block">$$q-\frac{r^2}{s}=\frac{196}{725},\qquad
2\delta-\frac{c^2}{s}=\frac{197}{2320},\qquad
-\frac{rc}{s}=\frac9{145}.$$</div>
<p>For example, $r^2/s=72^2/(175\cdot116)$; subtracting it from $92/175$ gives the first fraction. The second is $1/10-7/464$. Therefore</p>
<div class="math-block">$$\lambda_a=\sqrt{\frac{196/725}{197/2320}}
=\sqrt{\frac{3136}{985}}=\frac{56}{\sqrt{985}}\approx1.784308.$$</div>
<p>This lies inside $(0,144/35)$, so it minimizes its piece without clipping. The cost multiplier is</p>
<div class="math-block">$$\nu^*=\frac{72/175-\lambda_a/10}{116/175}
=\frac{18}{29}-\frac{35\lambda_a}{232}\approx0.351505\gt0.$$</div>
<p>Substitute in $x^*=(H^{-1}g-\nu^*H^{-1}b)/\lambda_a$. Writing $d_0=\sqrt{985}$ to keep the exact radical visible gives</p>
<div class="math-block">$$x^*=\left(\frac{2d_0+5}{290},\frac{65-3d_0}{580}\right)
\approx(0.233688,-0.050266).$$</div>
<p><strong>Check the unrounded constraints.</strong> The cost dot product is</p>
<div class="math-block">$$b^\top x^*
=\frac{3(2d_0+5)+2(65-3d_0)}{1450}
=\frac{145}{1450}=\frac1{10},$$</div>
<p>so $c+b^\top x^*=0$. For the trust cost, write $x_1=(4d_0+10)/580$, $x_2=(65-3d_0)/580$. Since $x^\top Hx=2x_1^2+x_1x_2+x_2^2$, its numerator after expansion is $29d_0^2+5075=29(985)+5075=33640$. Thus $\tfrac12(x^*)^\top Hx^*=33640/(2\cdot580^2)=1/20=\delta$.</p>
<p>The reward objective is</p>
<div class="math-block">$$g^\top x^*=x_1+\tfrac25x_2
=\frac{7\sqrt{985}+90}{1450}\approx0.213581.$$</div>
<p>The active dual piece has value $D_a(\lambda_a)=\sqrt{(196/725)(197/2320)}+9/145=(7\sqrt{985}+90)/1450$, exactly the same expression. This equality of a feasible primal value and a dual upper bound certifies optimality and zero gap.</p>
<p>For completeness, on the zero-cost-price piece $\lambda\ge144/35$, the unconstrained dual minimizer is $\sqrt{q/(2\delta)}=\sqrt{184/35}$, below that interval. Its projected minimizer is $\lambda_b=144/35$, giving $D_b=23/360+36/175=3397/12600\approx0.269603$, larger than $D_a$. Both candidates therefore select the positive-price solution. These are exact statements about the local quadratic subproblem; they do not by themselves certify the nonlinear policy's true cost.</p>
''')

replace(18,'Unpack the Gibbs normalization, monotone cost-price test and complementary-slackness switch between constraints. Show the numerical KL root and the exact temperature equation, retaining the fixed-temperature qualification.', ['Normalize the two exponential weights','Solve the monotone fixed-temperature cost bound','Distinguish exact dual multipliers when KL is slack','Bracket the tighter KL root and derive its temperature','Explain the fixed-temperature range and exact dual derivative'],r'''
<p><strong>(a) Normalize the two Gibbs weights.</strong> For $\lambda\gt0$, the penalized advantages are $(1-2\nu,-1+2\nu)$. Put $u=(1-2\nu)/\lambda$. The equal old probabilities cancel from the normalization, giving</p>
<div class="math-block">$$p=\frac{(1/2)e^u}{(1/2)e^u+(1/2)e^{-u}}
=\frac1{1+e^{-2u}}
=\sigma\!\left(\frac{2(1-2\nu)}{\lambda}\right).$$</div>
<p>This Gibbs formula needs a positive temperature $\lambda$. A zero optimal KL multiplier must be treated separately.</p>
<p><strong>(b) Hold the temperature at $1$ and price the cost.</strong> The expected cost advantage is $2p-2(1-p)=4p-2$. Its bound $4p-2\le0.5$ is equivalent to $p\le5/8$. At $\nu=0$, $p=\sigma(2)\approx0.880797$, which fails. As $\nu$ increases, the sigmoid argument decreases, so $p$ decreases; the smallest feasible $\nu$ makes the cost exactly tight.</p>
<p>The odds of $p=5/8$ are $(5/8)/(3/8)=5/3$. Taking their log gives $2(1-2\nu)=\ln(5/3)$, hence</p>
<div class="math-block">$$\nu=\frac12-\frac14\ln\frac53\approx0.372294,
\qquad p=\frac58.$$</div>
<p>The reward advantage is then $2p-1=1/4$, compared with $2\sigma(2)-1\approx0.761594$ without the cost constraint at that temperature.</p>
<p><strong>(c) Now solve both constraints, rather than fixing the temperature.</strong> The KL from $p=5/8$ to the old uniform law is</p>
<div class="math-block">$$K(5/8)=\frac58\ln\frac54+\frac38\ln\frac34
\approx0.031584\lt0.05.$$</div>
<p>Reward increases with $p$, and the cost constraint allows no $p\gt5/8$. Because $5/8$ itself passes the KL test, it is the exact optimizer. The KL constraint is slack, so complementary slackness forces its multiplier $\lambda^*=0$. The cost constraint is active; the remaining linear Lagrangian is $2p-1-\nu(4p-2.5)$, with derivative $2-4\nu$. Stationarity gives $\nu^*=1/2$. Thus the exact two-constraint multipliers are $(0,1/2)$, distinct from the fixed-temperature pair in (b), even though both produce the same policy.</p>
<p>At a fixed positive temperature, reproducing $p=5/8$ requires $\nu=1/2-(\lambda/4)\ln(5/3)$. This is nonnegative only for $\lambda\le2/\ln(5/3)\approx3.915230$. At hotter temperatures, the unconstrained Gibbs policy is already below the cost limit, so the correct cost price is zero and the policy is more conservative. For example, $\lambda=6$ gives $p=\sigma(1/3)\approx0.582570$. Fixed-temperature multiplier values should not be compared as if they were the exact multipliers of the original constrained problem.</p>
<p><strong>(d) Tighten KL to $0.02$.</strong> For a general $p$, $K(p)=p\ln(2p)+(1-p)\ln(2(1-p))$. Differentiation gives $K'(p)=\ln(p/(1-p))$, strictly positive for $p\gt1/2$. It starts at $K(1/2)=0$ and at $5/8$ exceeds $0.02$, so there is exactly one root $p^*\in(1/2,5/8)$ of $K(p^*)=0.02$. Numerically,</p>
<div class="math-block">$$K(0.59966520)\approx0.019999997334\lt0.02,
\qquad K(0.59966521)\approx0.020000001375\gt0.02.$$</div>
<p>Thus $0.59966520\lt p^*\lt0.59966521$, approximately $0.599665207$. This is the largest KL-feasible probability in the rewarding direction. Its cost advantage is $4p^*-2\approx0.398661\lt0.5$, so the cost constraint is slack and $\nu^*=0$. The KL constraint binds, and stationarity of $2p-1-\lambda(K(p)-0.02)$ gives</p>
<div class="math-block">$$2-\lambda^*\ln\frac{p^*}{1-p^*}=0,
\qquad\lambda^*=\frac2{\ln(p^*/(1-p^*))}\approx4.949633.$$</div>
<p>This is the same temperature that makes $\sigma(2/\lambda^*)=p^*$.</p>
<p>One can also verify dual optimality directly. With $\nu=0$, the normalizer is $\cosh(1/\lambda)$, so the dual is $\lambda\delta+\lambda\ln\cosh(1/\lambda)$. Its derivative is $\delta+\ln\cosh(1/\lambda)-\tanh(1/\lambda)/\lambda$. For $u=1/\lambda$, the Gibbs probabilities have log ratios to the uniform law $u-\ln\cosh u$ and $-u-\ln\cosh u$. Their average KL is therefore $u\tanh u-\ln\cosh u$. At $\delta=K(p^*)$, the dual derivative is zero. Here $\cosh u=(e^u+e^{-u})/2$ and $\tanh u=(e^u-e^{-u})/(e^u+e^{-u})$.</p>
<p>The exact multipliers exchange roles as the active constraint changes. Practical FOCOPS fixes a temperature, adapts the cost price and checks sampled KL; those choices approximate this policy-space problem rather than automatically solving both dual variables.</p>
''')

replace(19,'Provide complete piecewise/global minimization for the ReLU and quadratic penalties, solve and rationalize the barrier margin, and prove the equality-threshold counterexample without appealing to a generic neural-network guarantee.', ['Find the constrained optimizer and price','Analyze both ReLU pieces for all weights','Show the quadratic violation at every finite weight','Prove the barrier stationary point is its global minimum','Derive margin, objective gap and multiplier limits','Verify the strict-threshold counterexample'],r'''
<p><strong>(a) Solve the constrained problem.</strong> The allowed domain is $\theta\le1$. On it, $f'(\theta)=2(\theta-2)\lt0$, so $f$ decreases up to its right endpoint. Its unique minimum is $\bar\theta=1$, with value $1$. The minimization Lagrangian is $(\theta-2)^2+\lambda(\theta-1)$. Stationarity at $1$ gives $2(1-2)+\bar\lambda=0$, hence $\bar\lambda=2\ge0$. The constraint is active, so complementary slackness also holds.</p>
<p><strong>(b) Analyze the ReLU penalty by region.</strong> For $\theta\le1$, the penalty is zero and $F_\kappa$ decreases to its value $1$ at the boundary. For $\theta\gt1$,</p>
<div class="math-block">$$F_\kappa(\theta)=(\theta-2)^2+\kappa(\theta-1),
\qquad F_\kappa'(\theta)=2(\theta-2)+\kappa.$$</div>
<p>If $0\lt\kappa\lt2$, the derivative vanishes at $\theta_\kappa=2-\kappa/2\gt1$. It is negative before that point and positive after it, so this is the unique global minimizer. It violates the constraint by $\theta_\kappa-1=1-\kappa/2$; at $\kappa=1$ the minimizer is $1.5$.</p>
<p>If $\kappa\ge2$, then for every $\theta\gt1$, $F_\kappa'(\theta)=2(\theta-1)+(\kappa-2)\gt0$. Both pieces are therefore minimized at $1$. The finite exactness threshold in this strictly convex example is $\kappa\ge2=\bar\lambda$, including equality. This particular equality case does not establish equality-threshold exactness for every problem.</p>
<p><strong>(c) Compare a quadratic penalty.</strong> Let $\mu\gt0$. For $\theta\gt1$, stationarity of $(\theta-2)^2+(\mu/2)(\theta-1)^2$ gives</p>
<div class="math-block">$$2(\theta-2)+\mu(\theta-1)=0
\iff(2+\mu)\theta=4+\mu
\iff\theta_\mu=\frac{4+\mu}{2+\mu}=1+\frac2{2+\mu}.$$</div>
<p>This lies above $1$ for every finite $\mu$, and the derivative changes from negative to positive there, making it the unique minimizer. Its violation is $2/(2+\mu)$, decreasing like $1/\mu$: approximately $0.166667$ at $\mu=10$ and $0.019608$ at $\mu=100$. It approaches feasibility only as $\mu\to\infty$.</p>
<p><strong>Now solve the barrier on its proper domain.</strong> For $t\gt0$, IPO's example objective is $B_t(\theta)=(\theta-2)^2-(1/t)\ln(1-\theta)$, defined only for $\theta\lt1$. Its derivative is $2(\theta-2)+1/(t(1-\theta))$, and its second derivative is $2+1/(t(1-\theta)^2)\gt0$. It diverges at both ends of this domain, so its stationary point is the unique minimum.</p>
<p>Put $u=1-\theta\gt0$. The stationary equation becomes $-2(1+u)+1/(tu)=0$, or $2u^2+2u=1/t$. Its positive root is</p>
<div class="math-block">$$u=\frac{\sqrt{1+2/t}-1}{2}
=\frac1{t(\sqrt{1+2/t}+1)}.$$</div>
<p>The rationalized form shows $u\sim1/(2t)$ as $t\to\infty$, and $\theta_t=1-u$ is strictly feasible at every finite $t$. Its original-objective gap is</p>
<div class="math-block">$$f(\theta_t)-f(1)=(1+u)^2-1=2u+u^2
=\frac1t-u^2\le\frac1t,$$</div>
<p>where the last equality uses $2u+2u^2=1/t$. At $t=10$, $u\approx0.047723$ and the gap is $0.097723\lt0.1$.</p>
<p>The implied constraint multiplier is $\lambda_t=-1/(t\,g(\theta_t))=1/(tu)=1+\sqrt{1+2/t}$. It is approximately $2.095445$ at $t=10$ and $2.009950$ at $t=100$, tending to the constrained multiplier $2$. The barrier approaches the boundary from inside, whereas the quadratic penalty approaches it from outside. Only the ReLU penalty here is exact at a finite parameter.</p>
<p><strong>(d) Test equality at the price in a different problem.</strong> Minimize $-\theta$ subject to $\theta\le0$. The constrained minimum is at $0$ with multiplier $1$, since $-1+\bar\lambda=0$. At $\kappa=1$,</p>
<div class="math-block">$$-\theta+\max(0,\theta)=\begin{cases}-\theta,&\theta\le0,\\0,&\theta\ge0.
\end{cases}$$</div>
<p>Every $\theta\ge0$ minimizes this penalized objective, including infeasible $\theta\gt0$. For $\kappa\gt1$, the positive branch becomes $(\kappa-1)\theta\gt0$ and only $0$ minimizes it; for $\kappa\lt1$, that branch tends to $-\infty$ and no minimizer exists. This is why the general statement that <em>every</em> penalized minimizer is feasible needs $\kappa\gt\|\bar\lambda\|_\infty$ together with the theorem's saddle-point hypotheses. Stationarity alone for a nonconvex neural model would not supply those hypotheses.</p>
''')

RETAIN={
4:'The old value, both advantages, both policy-weighted averages and their distinct meanings are explicitly calculated. It states why a local advantage does not alone determine the global return change.',
5:'The total-variation absolute differences and directed probability-weighted log ratios are explicitly evaluated with natural logs. The specified KL direction and asymmetry are preserved.',
6:'The diagonal quadratic is expanded, each axis radius is obtained by setting the other coordinate to zero, and the test point is substituted into both the quadratic and original half-quadratic budget.',
7:'Both signed affine residuals are computed and assessed, and the solution expressly limits the conclusion to the local surrogate rather than the nonlinear true cost.',
8:'The inverse-gradient direction, normalizing dot product, optimizer, active quadratic and objective are worked. Cauchy-Schwarz supplies a genuine upper bound proving global optimality for this subproblem.',
9:'The coordinate projection and unchanged free coordinate are explained, then displacement, distance and half-squared objective are computed in the stated Euclidean metric.',
10:'Both numerators and squared denominators are substituted before division; the factor-of-45 comparison is explicit and distinguished from the actual surrogate error.',
11:'Both pessimistic upper bounds and budget checks are numerical, with the failed-bound-versus-true-unsafety distinction and confidence-event applicability stated.',
12:'The unconstrained optimizer is tested and fails, the upper-disk scalar objective and its derivative are given, and monotonicity selects and evaluates the constrained endpoint with both constraints active.',
13:'The linear and true residuals are separately evaluated, the positive quadratic root is displayed, and monotonicity on the nonnegative domain identifies the whole feasible interval and source of the prediction error.',
14:'Both likelihood ratios and their correctly weighted mean are computed; rare-action instability and the missing-support case are explained without pretending extrapolation restores an importance-sampling identity.',
15:'The failure union bound, joint success probability and both numerical margins are explicit. It requires the events to cover the selected update and uses no independence assumption.',
20:'All five parts are complete: per-task versus aggregate ratio interpretation, illustrative rate calculations and budget comparison, time-window distinction, inability to infer a ranking from aggregates, and the precise margin role of omitted shaping. It supplies the important source/benchmark qualifications.',
21:'Every data trajectory relevant to the feasible frontier is considered; initial and next tokens, exact relabeling offsets and the selected source trajectory are given. It explains infeasible requests, negative remaining-token distribution shift, and why conditioning/augmentation alone do not enforce a hard budget.',
}
assert len(replacements)==7 and len(RETAIN)==14
assert not set(replacements)&set(RETAIN)
assert set(replacements)|set(RETAIN)==set(range(1,22))
assert not (ROOT/OUT).exists() and not (ROOT/ARITHMETIC).exists()
baseline=json.loads((ROOT/BASELINE).read_bytes())
assert ref(baseline['source']['file'])['sha256']==baseline['source']['sha256']

checks=[]
def record(name,actual,expected=None,exact=True):
    if expected is not None:assert actual==expected,name
    checks.append({'name':name,'actual':str(actual),'expected':str(expected) if expected is not None else None,'exact_rational':exact})
record('B1 trust costs',(F(1,8),F(1,2)),(F(1,8),F(1,2)))
record('B1 cost residuals',(-F(1,5)+F(1,2),-F(1,5)),(F(3,10),-F(1,5)))
record('B3 original upper residual',F(1,5)*F(7,25),F(7,125))
record('B3 conservative upper residual',-F(1,5)+F(1,5)*F(1,4),-F(3,20))
record('9.1 old value',(F(1,2),F(3,2)),(F(1,2),F(3,2)))
record('9.1 both performance sums',(2*(F(1,2)*F(1,4)+F(1,2)*F(1,4)),2*(F(3,4)*F(1,4)+F(1,4)*F(1,4))),(F(1,2),F(1,2)))
q=F(16,35)+F(2,5)*F(6,35);r=F(4,35)+F(2,5)*F(26,35);s=F(3,5)*F(4,35)+F(4,5)*F(26,35)
record('9.2 q,r,s',(q,r,s),(F(92,175),F(72,175),F(116,175)))
record('9.2 hyperplane squared distance',F(1,100)/s,F(7,464))
record('9.2 reduced quadratic coefficient',q-r*r/s,F(196,725))
record('9.2 reduced radius coefficient',F(1,10)-F(1,100)/s,F(197,2320))
record('9.2 lambda squared',(q-r*r/s)/(F(1,10)-F(1,100)/s),F(3136,985))
rad=math.sqrt(985);la=56/rad;nu=18/29-35*la/232;x=((2*rad+5)/290,(65-3*rad)/580)
assert 0<la<144/35 and nu>0
assert abs(-.1+.6*x[0]+.8*x[1])<1e-14
assert abs(.5*(2*x[0]**2+x[0]*x[1]+x[1]**2)-.05)<1e-14
record('9.2 multipliers',(la,nu),exact=False)
record('9.2 optimizer',x,exact=False)
record('9.2 objective',(7*rad+90)/1450,exact=False)
record('9.2 exact cost cancellation',F(145,1450),F(1,10))
record('9.2 exact trust expansion',F(29*985+5075,2*580**2),F(1,20))
record('9.2 other dual candidate',F(23,360)+F(36,175),F(3397,12600))
def kl(p):return p*math.log(2*p)+(1-p)*math.log(2*(1-p))
assert kl(5/8)<.05 and kl(5/8)>.02
record('9.3 cost-limited probability',F(5,8),F(5,8))
record('9.3 fixed-temperature price',.5-.25*math.log(5/3),exact=False)
record('9.3 cost-limited KL',kl(5/8),exact=False)
low=0.59966520;high=0.59966521
assert kl(low)<.02<kl(high)
a=.5;b=.625
for _ in range(80):
    mid=(a+b)/2
    if kl(mid)<.02:a=mid
    else:b=mid
p=(a+b)/2;temperature=2/math.log(p/(1-p))
assert low<p<high and 4*p-2<.5
record('9.3 lower bracket KL',kl(low),exact=False)
record('9.3 upper bracket KL',kl(high),exact=False)
record('9.3 tighter-KL optimizer',p,exact=False)
record('9.3 tighter-KL temperature',temperature,exact=False)
u=1/temperature
assert abs(.02+math.log(math.cosh(u))-u*math.tanh(u))<1e-14
record('9.3 dual derivative float',.02+math.log(math.cosh(u))-u*math.tanh(u),exact=False)
record('9.4 quadratic violation mu10',F(2,12),F(1,6))
record('9.4 quadratic violation mu100',F(2,102),F(1,51))
for t in [10,100]:
    margin=(math.sqrt(1+2/t)-1)/2;price=1+math.sqrt(1+2/t)
    assert margin>0 and 2*margin+margin*margin<1/t
    record('9.4 barrier margin t'+str(t),margin,exact=False)
    record('9.4 barrier objective gap t'+str(t),2*margin+margin*margin,exact=False)
    record('9.4 barrier multiplier t'+str(t),price,exact=False)
arithmetic={'status':'passed_author_arithmetic_and_exact_rational_recomputations','author':'/root/review_gaussian35','page':'policy-optimization.html',
            'created_at_utc':datetime.now(timezone.utc).isoformat(),'checks':checks,
            'helper':ref('book/solutions/drafts/build-policy-optimization-thorough-v1.py'),
            'limits':'Native author arithmetic only. KL root brackets are numerical recomputations supplementing the exact implicit root; no new Lean compiler evidence, independent review or formal promotion is claimed.'}
(ROOT/ARITHMETIC).write_text(json.dumps(arithmetic,ensure_ascii=False,indent=2)+'\n')
rows=[]
for b in baseline['exercises']:
    n=b['ordinal'];decision='replace' if n in replacements else 'retain';body=replacements.get(n,b['solution']['html'])
    rows.append({'inventory_key':b['inventory_key'],'source_file':b['source_file'],'authoring_file':b['authoring_file'],'ordinal':n,'anchor':b['anchor'],'label':b['label'],
                 'original_source_sha256':b['source_sha256'],'original_authoring_source_sha256':b['authoring']['source_sha256'],
                 'original_question_sha256':b['problem']['sha256'],'original_hint_sha256':[h['disclosure']['sha256'] for h in b['hints']],
                 'original_solution_sha256':b['solution']['sha256'],'decision':decision,'replacement_html':body,'replacement_sha256':sha256(body.encode()).hexdigest(),
                 'thoroughness_rationale':rationales[n] if decision=='replace' else RETAIN[n],'specific_improvements':improvements.get(n,[]),
                 'whole_question_hint_answer_and_background_read':True,'pedagogical_status':'authored_pending_independent_review',
                 'question_hint_disclosure_notation_anchor_preservation_required':True})
draft={'schema':'individual_solution_draft_v1','status':'authored_pending_independent_review','author':'/root/review_gaussian35',
       'created_at_utc':datetime.now(timezone.utc).isoformat(),'page':'policy-optimization.html',
       'audience':'First-course linear algebra and single-variable calculus; explain additional local probability, policy and constrained-optimization concepts.',
       'baseline':ref(BASELINE),'baseline_manifest':ref('book/solutions/baseline-source90/manifest.json'),'inventory':baseline['inventory'],
       'page_contract':ref('page_contract.md'),'page_contract_fully_read':True,'criteria':ref('book/solutions/README.md'),
       'source_refs':[ref('SafeLearning/policy-optimization.html'),ref('book/chapters/policy-optimization.html')],
       'context_read':['Full canonical teaching text, all8 sections, assumptions, local/global guarantees, approximation caveats, method comparisons, benchmark conventions and application context',
                       'Full seven-step CPO interactive derivation data and explorer regime qualifications',
                       'Full authored application source and all21 questions, hints and original solutions'],
       'counts':{'reviewed_exercises':21,'replace':7,'retain':14,'book_lab_exercises':3},'exercises':rows,'arithmetic_report':ref(ARITHMETIC),
       'new_external_citations':[],'independent_pedagogical_approval_claimed':False,'rendered_qa_claimed':False,'whole_page_reserialized':False,
       'canonical_source_owner_selection_progress_publication_mutations':False,
       'scope':'Exact solution-body proposals only. Preserve all original questions, hints, disclosures, anchors, scripts, hooks, notation and qualified Source90 facts. Mirror lab replacements to their authored candidate. Root arranges independent review, QA and integration.',
       'helper':ref('book/solutions/drafts/build-policy-optimization-thorough-v1.py')}
(ROOT/OUT).write_text(json.dumps(draft,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'draft':ref(OUT),'arithmetic':ref(ARITHMETIC),'counts':draft['counts']},ensure_ascii=False))
