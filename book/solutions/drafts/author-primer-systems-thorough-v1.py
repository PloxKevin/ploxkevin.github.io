"""Prepare Source90 systems solution decisions without changing teaching sources."""
from pathlib import Path
from hashlib import sha256
import json

BASE = Path('book/solutions/baseline-source90/pages/primer-systems.html.json')
DEST = Path('book/solutions/drafts/primer-systems-thorough-solutions-v1.json')
replacement = {}
rationale = {}


def replace(anchor, why, body):
    replacement[anchor] = body.strip() + '\n'
    rationale[anchor] = why


replace('sys-extra-3', 'Show the equilibrium factorization, local deviation equations and Euler substitution; explain the approximation through its integral meaning.', r'''
<p>For continuous time an equilibrium has zero rate. Factor the right-hand side: $f(x)=-x+x^2=x(x-1)$. Thus the only equilibria are $x_*=0$ and $x_*=1$.</p>
<p>Let $\xi=x-x_*$ be a small deviation. The linearized equation is $\dot\xi=f'(x_*)\xi$, where $f'(x)=-1+2x$. At $0$ this gives $\dot\xi=-\xi$, whose solutions decay as $e^{-t}$; at $1$ it gives $\dot\xi=\xi$, whose nonzero solutions grow as $e^t$. Since the polynomial field is continuously differentiable, the indirect method makes $0$ locally exponentially stable and $1$ unstable. The conclusion at $0$ is local, not a claim about every initial state.</p>
<p>Forward Euler uses the starting rate throughout one time step:</p>
<div class="math-block">$$f(0.1)=-0.1+(0.1)^2=-0.09,\qquad x_{\rm next}=0.1+0.2(-0.09)=0.082.$$</div>
<p>The exact update would instead integrate the changing rate, $x(0.2)=0.1+\int_0^{0.2}f(x(s))\,ds$. Euler replaces that integral by $0.2f(0.1)$; as the state changes, so does $f(x(s))$. This is an approximation to a continuous trajectory.</p>
''')

replace('sys-extra-6', 'Derive the nilpotent power formula and explain its convergence for every initial state, rather than identifying stability only from one trajectory.', r'''
<p>Write $A=(1/2)I+N$ with $N=\begin{bmatrix}0&10\\0&0\end{bmatrix}$. Direct multiplication gives $N^2=0$, and $N$ commutes with the identity. The matrix binomial expansion therefore has only its terms with zero and one factors of $N$:</p>
<div class="math-block">$$A^t=\left(\frac12\right)^t I+t\left(\frac12\right)^{t-1}N,\qquad t\ge1.$$</div>
<p>The first coefficient comes from selecting the identity term in all $t$ factors; the second has $t$ choices for the one factor of $N$. Every term with two or more factors of $N$ is zero. For the specified start, $Nx_0=(10,0)^\top$, so</p>
<div class="math-block">$$x_t=A^tx_0=\begin{bmatrix}10t(1/2)^{t-1}\\(1/2)^t\end{bmatrix},\qquad x_1=(10,0.5)^\top.$$</div>
<p>Thus $\|x_1\|_2=\sqrt{100+0.25}\approx10.0125$, while $\|x_0\|_2=1$. Nevertheless both coefficients in $A^t$ tend to zero. For the polynomial-times-geometric term, the ratio of successive positive terms is $(t+1)/(2t)$, which is eventually at most $3/4$; it is then bounded by a decaying geometric sequence. Hence $A^t\to0$ and every trajectory converges to zero. Equivalently the two eigenvalues are $1/2$, so the linear system is Schur and asymptotically stable. Its transient Euclidean amplification can still matter for a state constraint.</p>
''')

replace('sys-extra-8', 'Display the matrix calculation and integrating-factor argument that converts the certificate inequality into a state-norm bound.', r'''
<p>Here $P=I$ is positive definite and $A$ is diagonal, so $A^\top=A$. Multiplication gives</p>
<div class="math-block">$$A^\top P+PA=A+A=\begin{bmatrix}-2&0\\0&-4\end{bmatrix}.$$</div>
<p>Both diagonal entries are negative. Applying the product rule to $V=x^\top Px=x_1^2+x_2^2$ along $\dot x=Ax$ gives</p>
<div class="math-block">$$\dot V=x^\top(A^\top P+PA)x=-2x_1^2-4x_2^2\le-2(x_1^2+x_2^2)=-2V.$$</div>
<p>Multiply by the integrating factor $e^{2t}$: $(e^{2t}V(t))'=e^{2t}(\dot V+2V)\le0$. Therefore $e^{2t}V(t)\le V(0)$, or $V(t)\le V(0)e^{-2t}$. Since $V=\|x\|_2^2$, taking nonnegative square roots yields $\|x(t)\|_2\le\|x(0)\|_2e^{-t}$. This bounds every trajectory of the stated linear system, with an explicit rate and prefactor.</p>
''')

replace('sys-extra-9', 'Prove invariance and forward existence before applying decay; separately explain the invariant but non-attractive boundary case.', r'''
<p>The chain rule gives $\dot V=2x\dot x=2x(-x+x^3)=-2x^2(1-x^2)$. The sublevel is the compact interval $S_c=[-\sqrt c,\sqrt c]$. For $0\lt c\lt1$ and $x\in S_c$, $x^2\le c$, hence $1-x^2\ge1-c\gt0$ and</p>
<div class="math-block">$$\dot V\le-2(1-c)x^2=-2(1-c)V.$$</div>
<p>At either endpoint, $V=c$ and $\dot V=-2c(1-c)\lt0$. Thus the vector field points strictly into the sublevel: a continuous trajectory cannot first cross from $V\le c$ to $V\gt c$ while its derivative at that boundary points downward. This proves forward invariance. The polynomial field is locally Lipschitz, so solutions are unique; staying in this compact interval also rules out finite escape and extends the solution for all forward time.</p>
<p>The integrating-factor inequality $(e^{2(1-c)t}V(t))'\le0$ now holds along the entire trajectory. It gives $V(t)\le V(0)e^{-2(1-c)t}$ and $|x(t)|\le|x_0|e^{-(1-c)t}\to0$.</p>
<p>For $c=1$, the interval $[-1,1]$ still stays invariant, but its endpoints satisfy $-x+x^3=0$. A trajectory starting at $1$ or $-1$ remains there, so not every state in this closed sublevel converges to zero. The strict coefficient $1-c$ disappears, exactly where those additional equilibria enter the set.</p>
''')

replace('sys-extra-10', 'Verify the defining monotonicity and growth properties for each function, including the zero derivative of r squared at the origin.', r'''
<p>Class $\mathcal K$ requires continuity on $[0,\infty)$, value zero at zero and strict increase. All three functions are continuous and vanish at zero. To check strictness, take $0\le r<s$:</p>
<div class="math-block">$$2s-2r=2(s-r)\gt0,\qquad s^2-r^2=(s-r)(s+r)\gt0,$$</div>
<div class="math-block">$$\frac{s}{1+s}-\frac{r}{1+r}=\frac{s-r}{(1+s)(1+r)}\gt0.$$</div>
<p>Thus all three are class $\mathcal K$. For $r^2$, a zero derivative at the single point $r=0$ does not prevent strict increase on the nonnegative domain.</p>
<p>Class $\mathcal K_\infty$ additionally requires unbounded growth. Both $2r$ and $r^2$ tend to infinity, so they are also class $\mathcal K_\infty$. In contrast, $r/(1+r)=1-1/(1+r)\to1$, so it is class $\mathcal K$ but not class $\mathcal K_\infty$.</p>
''')

replace('sys-extra-11', 'Derive the comparison bound with an integrating factor, solve the time inequality with the correct direction, and keep the guarantee exact.', r'''
<p>Multiply the differential inequality by the positive factor $e^{3t}$. The product rule gives $(e^{3t}V(t))'=e^{3t}(\dot V+3V)\le0$, so $e^{3t}V(t)\le V(0)=4$. Therefore $V(t)\le4e^{-3t}$.</p>
<p>It suffices to make this upper bound at most $0.2$. Solve:</p>
<div class="math-block">$$4e^{-3t}\le0.2\ \Longleftrightarrow\ e^{-3t}\le\frac1{20}\ \Longleftrightarrow\ -3t\le-\ln20\ \Longleftrightarrow\ t\ge\frac{\ln20}{3}.$$</div>
<p>The logarithm is increasing, and dividing by $-3$ reverses the last inequality. The exact sufficient entry time is $\ln20/3\approx0.9985774$ in the time units of the model; for example $t=1$ is sufficient. The same guarantee holds at every later time because the comparison upper bound keeps decreasing. The actual quantity may enter sooner if its derivative is more negative than the stated bound.</p>
''')

replace('sys-extra-12', 'Derive the input half-line, justify the closest-input projection, and connect its sign and boundary behavior to the all-time barrier inequality.', r'''
<p>The safe variable is $h(x)=1-x$, so its chain-rule derivative along $\dot x=u$ is $\dot h=-u$. Enforcing $\dot h\ge-2h$ gives $-u\ge-2(1-x)$; multiplying by $-1$ reverses the inequality, giving the allowable half-line $u\le2(1-x)$.</p>
<p>At $x=0.9$ the cap is $2(0.1)=0.2$. The desired input $1$ is outside that half-line. On $u\le0.2$, the squared distance $(u-1)^2$ decreases as $u$ increases toward $1$, so its minimum is the feasible endpoint $u=0.2$. In general the closest input is $u=\min\{1,2(1-x)\}$.</p>
<p>At the boundary $x=1$, admissibility becomes $u\le0$: the velocity can be tangent or point away from the wall, but cannot point beyond it. To obtain the trajectory guarantee, enforce the constraint continuously. Then</p>
<div class="math-block">$$\frac{d}{dt}\big(e^{2t}h(x(t))\big)=e^{2t}(\dot h+2h)\ge0,\qquad h(x(t))\ge h(x_0)e^{-2t}\ge0.$$</div>
<p>This applies to initially safe states along an existing closed-loop solution; the displayed continuous filter is locally Lipschitz, so it has unique trajectories. An input selected from one sampled value is not automatically this continuously enforced filter: the cap must remain valid as the state moves.</p>
''')

replace('sys-extra-14', 'Solve both Riccati roots and explain the optimal feedback through a completed square and the stabilizing/nonnegative value requirement.', r'''
<p>Rearrange the supplied Riccati equation: $2P-P^2+1=0$ becomes $P^2-2P-1=0$, or $(P-1)^2=2$. Its roots are $1\pm\sqrt2$. The positive root is $P=1+\sqrt2\approx2.414214$.</p>
<p>To see the feedback, insert $V(x)=Px^2$ into the continuous Bellman expression for $\dot x=x+u$:</p>
<div class="math-block">$$x^2+u^2+V'(x)(x+u)=x^2+u^2+2Px(x+u)=(u+Px)^2+(1+2P-P^2)x^2.$$</div>
<p>The Riccati equation makes the last coefficient zero. The remaining square is minimized by the unconstrained input $u_*=-Px$. Substitution into the plant gives $\dot x=(1-P)x=-\sqrt2\,x$, hence $x(t)=x_0e^{-\sqrt2 t}$. It converges exponentially, and both squared state and input have finite integrals.</p>
<p>The other root $1-\sqrt2\lt0$ would make $V$ negative for nonzero states even though the cost is nonnegative, and gives rate $1-P=+\sqrt2$. It is not the stabilizing value-function solution. Here the scalar plant is controllable and the positive state penalty detects its mode, as required by the LQR result.</p>
''')

replace('sys-extra-15', 'Make the impossibility statement an all-time integrating-factor lower bound, then state the exact region in which the unsaturated feedback is admissible.', r'''
<p>The most negative admissible input is $u=-1$. Every input satisfying $|u|\le1$ therefore gives $\dot x=2x+u\ge2x-1$. Put $e=x-1/2$; then $\dot e\ge2e$. Multiplying by $e^{-2t}$ gives $(e^{-2t}e(t))'\ge0$, so</p>
<div class="math-block">$$x(t)\ge\frac12+\left(x_0-\frac12\right)e^{2t}.$$</div>
<p>If $x_0\gt1/2$, the right side is always above $1/2$ and grows. No admissible input can make this state return toward zero or cross downward into the inner region. For bounded piecewise-continuous inputs the forced linear equation has a global solution; this lower bound holds for every forward time.</p>
<p>The requested feedback $u=-3x$ lies within the actuator range precisely when $3|x|\le1$, or $|x|\le1/3$. In that interval the actual unsaturated closed loop is $\dot x=2x-3x=-x$. Starting there keeps the state there as it decays, so it supplies a local stabilizing design. Outside it the clipped controller has different dynamics, and the impossibility bound above rules out a global stabilization claim under these input limits.</p>
''')

replace('sys-extra-20', 'Show exactly where the zero-at-zero Lipschitz hypothesis enters, derive the exponential bound, and state the small-gain and existence conditions.', r'''
<p>The condition $\varphi(0)=0$ lets the Lipschitz bound compare with the origin: $|\varphi(x)|=|\varphi(x)-\varphi(0)|\le|x|$. Thus $x\varphi(x)\le|x|\,|\varphi(x)|\le x^2$, including both signs of $x$.</p>
<p>For $V=x^2$, the chain rule gives</p>
<div class="math-block">$$\dot V=2x[-x+0.8\varphi(x)]=-2x^2+1.6x\varphi(x)\le-2x^2+1.6x^2=-0.4V.$$</div>
<p>The integrating factor $e^{0.4t}$ yields $V(t)\le V(0)e^{-0.4t}$. Taking square roots gives $|x(t)|\le|x_0|e^{-0.2t}$ for every initial state. The field $-x+0.8\varphi(x)$ is globally Lipschitz with constant at most $1+0.8=1.8$, so its unique solutions exist for all forward time. The estimate therefore proves global exponential stability.</p>
<p>For the same loop, the linear block $G(s)=0.8/(s+1)$ has induced $L_2$ gain $\sup_\omega0.8/\sqrt{1+\omega^2}=0.8$. Pointwise $|\varphi(x)|\le|x|$ gives gain at most $1$ for the memoryless block. There is no algebraic feedthrough loop, and the product $0.8\cdot1\lt1$ meets the small-gain condition. The direct derivative proof also provides an explicit state-decay rate.</p>
''')

replace('sys-extra-26', 'Work out both minimizations and value functions by completed squares, then check the resulting controls and total cost.', r'''
<p>Solve the last decision first. At a state $x$ with one decision left,</p>
<div class="math-block">$$u^2+(x+u)^2=2u^2+2xu+x^2=2\left(u+\frac x2\right)^2+\frac{x^2}{2}.$$</div>
<p>The square is nonnegative and is zero only at $u=-x/2$, so $V_1(x)=x^2/2$. This expresses the best remaining cost as a function of the state reached after the first action.</p>
<p>Starting from $x_0=3$, Bellman's first objective is the effort $u_0^2$ plus that optimal tail cost:</p>
<div class="math-block">$$u_0^2+V_1(3+u_0)=u_0^2+\frac{(3+u_0)^2}{2}=\frac32u_0^2+3u_0+\frac92=\frac32(u_0+1)^2+3.$$</div>
<p>Its unique minimum is $u_0=-1$, giving $x_1=3-1=2$. The final-step feedback then gives $u_1=-x_1/2=-1$ and $x_2=2-1=1$. Directly the cost is $(-1)^2+(-1)^2+1^2=3$, agreeing with the first value minimum. The future action was optimized for the successor state, which is the reason to use the backward recursion.</p>
''')

replace('sys-extra-27', 'Index the shifted plan and show every appended input/state constraint, including the length-one case and the exact-model assumption.', r'''
<p>For any terminal state $x\in X_f=[-0.5,0.5]$, choose $\kappa_f(x)=-x$. Then $|\kappa_f(x)|=|x|\le0.5\le1$, and the successor is $x+\kappa_f(x)=0\in X_f$. The whole terminal set also obeys $|x|\le2$. Thus the terminal feedback is admissible and keeps the terminal set invariant.</p>
<p>Let a feasible length-$N$ plan, $N\ge1$, have states $x_0,\ldots,x_N$ and inputs $u_0,\ldots,u_{N-1}$, with $x_N\in X_f$. After executing $u_0$, the measured next state is exactly $x_1$ because there is no disturbance or model error. Use the candidate inputs</p>
<div class="math-block">$$(u_1,\ldots,u_{N-1},-x_N).$$</div>
<p>The first $N-1$ predicted transitions reproduce the feasible tail $x_1,\ldots,x_N$ of the old plan. The last input has magnitude at most $0.5$, and its successor is zero in $X_f$. Hence every input and state constraint, and the new terminal constraint, hold. For $N=1$ the old tail is empty and the candidate consists only of $-x_1$, with the same argument.</p>
<p>A feasible candidate proves that the next optimization problem has a feasible plan. Repeating the construction proves recursive feasibility from an initially feasible state. It does not by itself establish cost decrease or stability; those need terminal-cost assumptions. Disturbances would also break the exact equality with the old predicted $x_1$ and require a robustness margin.</p>
''')

replace('book-d-b1', 'Restore the held-input model and units, compute each candidate reading, and verify commands and intervening temperatures.', r'''
<p>Example 1 uses five-minute holds with $a=e^{-1/4}$, $b=4(1-a)$, and gain $0.5$ kW per degree Celsius. Thus $q=a-0.5b=3a-2\approx0.3364023492$, and the starting error is $x_0=20-22=-2\,{}^\circ\mathrm C$. The reading errors obey $x_k=q^kx_0$.</p>
<p>The first eligible reading is found by checking integer $k$, since the requirement is at a reading:</p>
<div class="math-block">$$|x_0|=2,\qquad |x_1|=2q\approx0.6728047,\qquad |x_2|=2q^2\approx0.2263331\quad({}^\circ\mathrm C).$$</div>
<p>The first two values exceed $0.3$ and the third is below it. Hence $k=2$ is the first qualifying reading, at $2(5)=10$ minutes. Its temperature is about $22-0.2263331=21.7736669\,{}^\circ\mathrm C$.</p>
<p>The two inputs held before that reading are $u_0=1-0.5(-2)=2$ kW and $u_1=1-0.5(-2q)=1+q\approx1.3364023$ kW. Both obey $0\le u\le2$. More generally $|x_k|\le2$ keeps this command admissible. During each hold, $x(k\Delta+s)=(3e^{-0.05s}-2)x_k$ with $0\le s\le5$; the multiplier decreases from $1$ to the positive $q$. Each temperature stays between its adjacent readings, so these holds also remain in the model's allowed temperature interval.</p>
''')

replace('book-d-b2', 'Derive necessity and sufficiency of the worst-case sampled interval bound, preserve exact gain endpoints, and independently enforce the heater range.', r'''
<p>Use the exact coefficients $a=e^{-1/4}$ and $b=4(1-a)\gt0$. For $0\le k\le0.5$, the closed-loop multiplier $q_k=a-bk$ is positive: its smallest value is $a-0.5b=3a-2\approx0.3364023$.</p>
<p>For $|x|\le0.2$ and $|w|\le0.1$ degrees Celsius, the next sampled error satisfies $|q_kx+w|\le0.2q_k+0.1$. Equal signs at the extreme state and disturbance attain this bound, so it gives the exact one-step invariance condition:</p>
<div class="math-block">$$0.2q_k+0.1\le0.2\ \Longleftrightarrow\ q_k\le0.5\ \Longleftrightarrow\ a-bk\le0.5\ \Longleftrightarrow\ k\ge\frac{a-0.5}{b}.$$</div>
<p>Commands throughout $|x_k|\le2$ must also obey $0\le1-kx_k\le2$. For nonnegative $k$, the smallest and largest commands are $1-2k$ and $1+2k$; both are admissible precisely when $k\le0.5$. Combining the requirements gives</p>
<div class="math-block">$$k\in\left[\frac{e^{-1/4}-0.5}{4(1-e^{-1/4})},\,0.5\right]\quad\text{kW per degree Celsius}.$$</div>
<p>The lower endpoint is approximately $0.31510146$; the exact expression defines the guarantee, since rounding it downward would slightly weaken the required bound. For any gain in this interval, induction keeps an initially sampled error in $[-0.2,0.2]$. This does not prove when a state outside that set enters it. The disturbance assumption concerns sampled updates and supplies no independent bound on excursions between readings.</p>
''')

replace('book-d-b3', 'Derive the worst stopping-distance expression from coasting plus braking, establish the monotone worst case, and solve the exact delay bound.', r'''
<p>If the speed is $v$, the distance is $d$ and available braking magnitude is $a_b$, coasting for $\tau$ consumes $v\tau$ metres. Full braking then consumes $v^2/(2a_b)$ metres: integrating $v-a_bt$ until $t=v/a_b$ gives that formula. Thus nonnegative final clearance requires $v\tau+v^2/(2a_b)\le d$.</p>
<p>For nonnegative speeds and delays, travel increases with $v$ and decreases with $a_b$. The most difficult allowed state therefore has $d=0.72$ m, $v=1.1$ m/s and $a_b=1$ m/s$^2$. At the proposed delay,</p>
<div class="math-block">$$1.1(0.2)+\frac{1.1^2}{2(1)}=0.22+0.605=0.825\ \mathrm m\gt0.72\ \mathrm m.$$</div>
<p>This allowed case needs $0.105$ m more than is available, so $d\ge0$ is not guaranteed by the delayed-braking strategy. It is an actual counterexample under the model, not merely a failed sufficient estimate.</p>
<p>To certify every allowed state, solve the worst-case inequality:</p>
<div class="math-block">$$1.1\tau+0.605\le0.72\ \Longleftrightarrow\ \tau\le\frac{0.115}{1.1}=\frac{23}{220}\ \mathrm s\approx0.10454545\ \mathrm s.$$</div>
<p>This exact bound is the largest certified delay when zero final clearance is allowed: the worst case reaches the wall exactly at stopping at equality. A strictly positive clearance would require a smaller delay or an added margin. The calculation assumes the whole measurement intervals are possible, speed is constant while coasting, and at least the stated braking acceleration is available until rest. Midpoints would incorrectly predict $1(0.2)+1^2/2=0.7\le0.75$, omitting those permitted extremes.</p>
''')

replace('book-d-b4', 'Derive the saturated map, check both first-step predictions, prove its interval image piecewise, and justify the extension between readings.', r'''
<p>Keep $a=e^{-1/4}\approx0.7788007831$ and $b=4(1-a)\approx0.8847968677$. Without clipping, $v=u-1=-x$ gives $x_{k+1}=(a-b)x_k$, with $a-b=5a-4\approx-0.1059960846$. From $x_0=-2$, this formula predicts $x_1=-2(a-b)\approx0.2119921693$.</p>
<p>But the requested command is $u_0=1-(-2)=3$ kW. It clips to $2$ kW, so the actual held deviation is $v_0=1$ and the actual first reading is $x_1=-2a+b=4-6a\approx-0.6728046984$ degrees Celsius.</p>
<p>Clipping gives the following continuous piecewise-affine sampled map:</p>
<div class="math-block">$$F(x)=\begin{cases}ax+b,&-2\le x\le-1,\\(a-b)x,&-1\le x\le1,\\ax-b,&1\le x\le2.\end{cases}$$</div>
<p>On the outer pieces the slope $a$ is positive, so checking their endpoints gives the whole image interval. On the middle piece the slope $a-b$ is negative, reversing endpoint order:</p>
<ul><li>$F([-2,-1])=[4-6a,\,4-5a]\approx[-0.6728047,0.1059961]$.</li><li>$F([-1,1])=[5a-4,\,4-5a]\approx[-0.1059961,0.1059961]$.</li><li>$F([1,2])=[5a-4,\,6a-4]\approx[-0.1059961,0.6728047]$.</li></ul>
<p>Every image lies in $[-2,2]$. Starting there, induction therefore preserves the interval at every reading, and clipping itself enforces the heater limits. The exact expressions define these intervals; displayed decimals are approximations.</p>
<p>For a fixed held $v_k$, the continuous trajectory is $x(k\Delta+s)=4v_k+(x_k-4v_k)e^{-0.05s}$. Its derivative has a constant sign during the hold, or is zero throughout, so it lies between its two sampled endpoints. Hence the full temperature trajectory also stays in $[-2,2]$ error. The unclipped linear multiplier only applies where $|x|\le1$.</p>
''')

replace('exercise-35', 'Work every pendulum equilibrium and Jacobian calculation, distinguish local nonlinear conclusions, and compute the Euler and exact sampled moduli explicitly.', r'''
<p><strong>(a) Equilibria.</strong> With $x_1=\theta$ and $x_2=\dot\theta$, the unforced equations are $\dot x_1=x_2$ and $\dot x_2=10\sin x_1-0.1x_2$. Zero rates require $x_2=0$ and $\sin x_1=0$. Thus $(\theta,\dot\theta)=(m\pi,0)$ for every integer $m$: modulo $2\pi$, these are upright $(0,0)$ and hanging $(\pi,0)$.</p>
<p><strong>(b) Linearizations.</strong> Differentiating the vector field gives $A(\theta_*)=\begin{bmatrix}0&1\\10\cos\theta_*&-0.1\end{bmatrix}$. At $0$,</p>
<div class="math-block">$$A_0=\begin{bmatrix}0&1\\10&-0.1\end{bmatrix},\qquad \det(\lambda I-A_0)=\lambda(\lambda+0.1)-10.$$</div>
<p>The roots are $\lambda=(-0.1\pm\sqrt{40.01})/2\approx3.112673,-3.212673$. One positive and one negative mode make a saddle; the positive eigenvalue proves the nonlinear upright equilibrium is unstable.</p>
<p>At $\pi$, $\cos\pi=-1$, so</p>
<div class="math-block">$$A_\pi=\begin{bmatrix}0&1\\-10&-0.1\end{bmatrix},\qquad \det(\lambda I-A_\pi)=\lambda^2+0.1\lambda+10.$$</div>
<p>The discriminant is $0.01-40=-39.99$, yielding $\lambda=-0.05\pm j\sqrt{39.99}/2\approx-0.05\pm3.161882j$. Both real parts are negative, so the linearization is a stable focus. The smooth nonlinear model is consequently locally exponentially stable near the hanging equilibrium.</p>
<p><strong>(c) Euler versus exact sampling.</strong> Deviations from the hanging equilibrium obey the Euler map $\xi_{k+1}=(I+0.1A_\pi)\xi_k$, whose matrix is $\begin{bmatrix}1&0.1\\-1&0.99\end{bmatrix}$. Each eigenvalue becomes $1+0.1\lambda=0.995\pm j\sqrt{39.99}/20$. Hence</p>
<div class="math-block">$$|1+0.1\lambda|^2=0.995^2+\frac{39.99}{400}=0.990025+0.099975=1.09.$$</div>
<p>Its modulus is $\sqrt{1.09}\approx1.04403\gt1$, so this numerical model has growing oscillations. Exact sampling of the linear flow uses $e^{0.1A_\pi}$, whose eigenvalues are $e^{0.1\lambda}$ with modulus $e^{0.1(-0.05)}=e^{-0.005}\approx0.995012\lt1$. The continuous linear dynamics decay, while this Euler step is unstable. A continuous-time stability result must therefore be checked again for the chosen discrete approximation.</p>
''')

replace('exercise-36', 'Expand trace and determinant, derive each strict Schur inequality, and explain sustained versus damped oscillations without confusing nominal cycle length with periodic decay.', r'''
<p><strong>(a)</strong> Trace adds the diagonal entries. The determinant subtracts the off-diagonal product:</p>
<div class="math-block">$$\tau=2-c(K_P+K_I),\qquad \Delta=[1-c(K_P+K_I)](1)-(-cK_I)(1)=1-cK_P.$$</div>
<p><strong>(b)</strong> With $K_P=0$, $\Delta=1$ and $\tau=2-cK_I$. The roots of $\lambda^2-\tau\lambda+1=0$ are complex exactly when $\tau^2\lt4$, or $-2\lt2-cK_I\lt2$, equivalently $0\lt cK_I\lt4$. Real matrices have conjugate roots; their product is then $\lambda\bar\lambda=|\lambda|^2=\Delta=1$. They lie on the unit circle and do not decay.</p>
<p>Write $\lambda=e^{\pm j\vartheta}$, so $2\cos\vartheta=\tau$. At $cK_I=1$, $\cos\vartheta=1/2$ and $\vartheta=\pi/3$. The distinct eigenvalues each satisfy $\lambda^6=1$ and no smaller positive power is $1$. The diagonalizable matrix therefore has $M^6=I$, and each nonzero real trajectory repeats after six steps. The boundary values $cK_I=0,4$ have repeated real roots and are outside the complex-root argument.</p>
<p><strong>(c)</strong> The $2\times2$ Schur test requires $|\Delta|\lt1$ and $-1-\Delta\lt\tau\lt1+\Delta$. Substitute the actual trace and determinant and rearrange:</p>
<div class="math-block">$$\begin{aligned}|1-cK_P|\lt1&\ \Longleftrightarrow\ 0\lt cK_P\lt2,\\2-c(K_P+K_I)\lt2-cK_P&\ \Longleftrightarrow\ cK_I\gt0,\\-2+c(K_P+K_I)\lt2-cK_P&\ \Longleftrightarrow\ c(2K_P+K_I)\lt4.\end{aligned}$$</div>
<p>These simultaneous strict inequalities give the exact stability region. Equality would admit a unit-modulus eigenvalue rather than asymptotic decay.</p>
<p><strong>(d)</strong> For $c=1$ and $K_P=K_I=0.5$, $\tau=1$ and $\Delta=0.5$. The three checks are $0\lt0.5\lt2$, $0.5\gt0$, and $1.5\lt4$, so the loop is Schur. Solving $\lambda^2-\lambda+0.5=0$ gives $\lambda=0.5\pm0.5j$, modulus $\sqrt{0.5}\approx0.707107$ and angle $\pi/4$. There is a nominal eight-step oscillation cycle, but the full trajectory does not repeat: its envelope shrinks by $\sqrt{0.5}$ per step. The proportional term supplies damping to this integral loop.</p>
''')

replace('exercise-37', 'Show every Lyapunov equation entry and strict sublevel condition, then prove the full asymmetric region of attraction with all boundary and exterior cases.', r'''
<p><strong>(a)</strong> Write the symmetric unknown as $P=\begin{bmatrix}p_1&p_2\\p_2&p_3\end{bmatrix}$. Multiplication by the given $A$ yields</p>
<div class="math-block">$$A^\top P+PA=\begin{bmatrix}-2p_2&p_1-p_2-p_3\\p_1-p_2-p_3&2p_2-2p_3\end{bmatrix}=-I.$$</div>
<p>The upper-left equation gives $p_2=1/2$. The lower-right then gives $1-2p_3=-1$, hence $p_3=1$. The off-diagonal equation gives $p_1=p_2+p_3=3/2$. Thus $P=\begin{bmatrix}3/2&1/2\\1/2&1\end{bmatrix}$. Its first leading minor is $3/2\gt0$, and its determinant is $3/2-1/4=5/4\gt0$, so Sylvester's criterion proves $P\succ0$. As a direct check, $A^\top P=\begin{bmatrix}-1/2&-1\\1&-1/2\end{bmatrix}$, whose sum with its transpose is $-I$. Consequently $\dot V=-\|x\|_2^2$ for this linear system.</p>
<p><strong>(b)</strong> For the scalar map $g(x)=x(1/2+x)$ and $V=x^2$,</p>
<div class="math-block">$$\Delta V=V(g(x))-V(x)=x^2\big[(1/2+x)^2-1\big].$$</div>
<p>At $x=0$ the difference is zero. At nonzero $x$ it is negative exactly when $|1/2+x|\lt1$, or $-3/2\lt x\lt1/2$. A positive sublevel $V\le c$ is $[-\sqrt c,\sqrt c]$, which must have strict decrease at every nonzero point. Its positive endpoint imposes $\sqrt c\lt1/2$, hence $0\lt c\lt1/4$. Each such compact sublevel satisfies the theorem, since $g$ and $V$ are continuous and $g(0)=0$. Their union gives the certified region $(-1/2,1/2)$. At $c=1/4$ the included fixed point $1/2$ prevents strict decrease and convergence.</p>
<p><strong>(c)</strong> The full basin is larger. Solving $g(x)=x$ gives fixed points $0,1/2$, and $g(-1)=1/2$. For $-1\lt x\lt1/2$, complete the square and factor relative to the upper endpoint:</p>
<div class="math-block">$$g(x)=(x+1/4)^2-1/16\ge-1/16,\qquad g(x)-1/2=(x+1)(x-1/2)\lt0.$$</div>
<p>Thus after one step $y=g(x_0)$ lies in $[-1/16,1/2)$, with $r=|y|\lt1/2$. Whenever $|x_t|\le r$, $|g(x_t)|\le|x_t|(1/2+r)$, where $1/2+r\lt1$. Induction preserves this bound and gives geometric convergence to zero. This proves attraction for every $x_0\in(-1,1/2)$.</p>
<p>The boundary starts $x_0=-1$ and $x_0=1/2$ settle at the nonzero fixed point. If $x_0\gt1/2$, then $g(x)-x=x(x-1/2)\gt0$ throughout that region, so the iterates increase. A finite limit would have to be a fixed point greater than $1/2$, which does not exist; they diverge. If $x_0\lt-1$, the same factorization gives $g(x_0)\gt1/2$, reducing to that divergent case. Hence the true region of attraction is exactly $(-1,1/2)$. The symmetric sublevels of $x^2$ certify a conservative subset of this asymmetric basin.</p>
''')

replace('exercise-38', 'Derive the affine comparison solution, show the input projection and switching time, and verify the barrier bound on each trajectory piece.', r'''
<p><strong>(a)</strong> Shift by the comparison equilibrium: $z=v-1/2$ satisfies $\dot z\le-2z$ and $z(0)=5/2$. The integrating factor gives $(e^{2t}z)'\le0$, hence</p>
<div class="math-block">$$v(t)\le\frac12+\frac52e^{-2t}.$$</div>
<p>This is also the solution of the equality comparison equation $\dot w=-2w+1$, whose right-hand side is globally Lipschitz.</p>
<p><strong>(b)</strong> Along $\dot x=u$, $\dot h=-u$. The CBF inequality is $-u+2(1-x)\ge0$, so $K_{\rm cbf}(x)=\{u:u\le2(1-x)\}$. Projecting a desired input onto this half-line gives $u=\min\{u_{\rm nom},2(1-x)\}$. At $x=0$ the cap is $2$, so $u=1$ passes unchanged. At $x=0.8$ the cap is $0.4$, so the filtered command is $0.4$.</p>
<p><strong>(c)</strong> Starting at $x_0=0$, the desired speed $1$ is allowed while $2(1-x)\ge1$, equivalently $x\le1/2$. Then $\dot x=1$ gives $x(t)=t$, reaching the switch at $t=1/2$. After that the active cap gives $\dot x=2(1-x)$; its distance to the wall solves $\dot h=-2h$ with $h(1/2)=1/2$. Therefore</p>
<div class="math-block">$$x(t)=\begin{cases}t,&0\le t\le1/2,\\1-\tfrac12e^{-2(t-1/2)},&t\ge1/2,\end{cases}\qquad h(x(t))=\begin{cases}1-t,&0\le t\le1/2,\\\tfrac12e^{-2(t-1/2)},&t\ge1/2.\end{cases}$$</div>
<p>To verify the requested lower bound, on the first interval set $d(t)=1-t-e^{-2t}$. Its second derivative is $-4e^{-2t}\lt0$, so it is concave; its endpoint values are $d(0)=0$ and $d(1/2)=1/2-e^{-1}\gt0$. It lies above the nonnegative chord between those endpoints. Thus $1-t\ge e^{-2t}$. On the second interval, $h=(e/2)e^{-2t}\ge e^{-2t}$ because $e/2\gt1$. Since $h(x_0)=1$, both pieces establish $h(x(t))\ge h(x_0)e^{-2t}\gt0$ for finite time. The controller approaches the wall without crossing it.</p>
''')

replace('exercise-39', 'Expand the DARE and exact gain-factor inequalities, then derive the PI augmented-state matrix with the stated integrator timing and check its equilibrium.', r'''
<p><strong>(a) LQR and gain margin.</strong> With $a=1.2$ and $b=q=r=1$, the scalar DARE is $p=1+1.44p-1.44p^2/(1+p)$. The nonnegative stabilizing solution has $1+p\gt0$. Multiplying through gives</p>
<div class="math-block">$$p+p^2=(1+p)+1.44p(1+p)-1.44p^2=1+2.44p,\qquad p^2-1.44p-1=0.$$</div>
<p>The positive root is $p=[1.44+\sqrt{1.44^2+4}]/2\approx1.952233744$. It gives $K=1.2p/(1+p)\approx0.793528120$ and closed-loop pole $1.2-K\approx0.406471880$, inside the unit disk. The negative root is incompatible with a nonnegative quadratic value for this positive cost. The plant is controllable and its positive state penalty detects the unstable mode, satisfying the LQR assumptions.</p>
<p>Scaling the input gain to $u=-\kappa Kx$ changes the pole to $1.2-\kappa K$. As $K\gt0$, discrete-time stability requires</p>
<div class="math-block">$$-1\lt1.2-\kappa K\lt1\ \Longleftrightarrow\ 0.2\lt\kappa K\lt2.2\ \Longleftrightarrow\ \frac{0.2}{K}\lt\kappa\lt\frac{2.2}{K}.$$</div>
<p>The exact endpoints are approximately $0.252038957$ and $2.772428531$. The interval is open: its endpoints give poles $1$ and $-1$. Use the exact expressions to state the margin; rounded decimals are estimates. Because the open-loop plant is unstable, a sufficiently small positive feedback scale also fails to stabilize it.</p>
<p><strong>(b) P and PI steady states.</strong> P-only feedback gives $x_{t+1}=0.8x_t+0.5(1-x_t)+0.5=0.3x_t+1$. The coefficient $0.3$ is Schur. Its equilibrium solves $x_*=0.3x_*+1$, giving $x_*=10/7$ and tracking error $1-x_*=-3/7$.</p>
<p>Use the page's PI timing: $e_t=1-x_t$, $I_t=I_{t-1}+e_t$ and $u_t=0.5e_t+0.2I_t=0.7e_t+0.2I_{t-1}$. Substitution into the plant and integrator yields</p>
<div class="math-block">$$\begin{bmatrix}x_{t+1}\\I_t\end{bmatrix}=\begin{bmatrix}0.1&0.2\\-1&1\end{bmatrix}\begin{bmatrix}x_t\\I_{t-1}\end{bmatrix}+\begin{bmatrix}1.2\\1\end{bmatrix}.$$</div>
<p>Deviations from its equilibrium follow this matrix. Its trace is $1.1$ and determinant is $0.1+0.2=0.3$, so the characteristic polynomial is $\lambda^2-1.1\lambda+0.3=(\lambda-0.6)(\lambda-0.5)$. Both eigenvalues are inside the unit disk, proving convergence.</p>
<p>At equilibrium the integrator satisfies $I_t=I_{t-1}$, forcing $e_*=0$ and $x_*=1$. The plant balance is $1=0.8+u_*+0.5$, so $u_*=-0.3$. Since P contributes zero at zero error, $0.2I_*=-0.3$, giving $I_*=-1.5$. Integral action supplies the steady input needed to cancel the constant disturbance, with convergence separately verified.</p>
''')

replace('exercise-40', 'Show impulse-response indexing, frequency and geometric gains, exact Gramian agreement, and the full storage telescoping proof.', r'''
<p><strong>(a)</strong> With a unit impulse $w_0=1$ and later inputs zero, the zero initial state gives $x_1=1$, $x_2=0.8$, and so on. There is no direct feedthrough, so</p>
<div class="math-block">$$h_0=0,\qquad h_k=0.6(0.8)^{k-1}\ (k\ge1),\qquad H(z)=\sum_{k=1}^{\infty}0.6(0.8)^{k-1}z^{-k}=\frac{0.6}{z-0.8}.$$</div>
<p>The geometric transform converges for $|z|\gt0.8$, including the unit circle, and the pole $0.8$ is stable.</p>
<p><strong>(b)</strong> The impulse response is nonnegative. Summing its magnitudes gives $\|h\|_1=0.6/(1-0.8)=3$, which is the induced peak gain: convolution gives $|z_t|\le3\|w\|_\infty$, and a constant unit input has outputs tending to $3$.</p>
<p>For the energy gain, $|e^{j\omega}-0.8|^2=(\cos\omega-0.8)^2+\sin^2\omega=1.64-1.6\cos\omega$. This denominator is smallest at $\cos\omega=1$, where its square root is $0.2$. Therefore $\|H\|_\infty=0.6/0.2=3$, the zero-state induced $\ell_2$ gain by the stable-LTI theorem.</p>
<p>The impulse-response energy instead gives</p>
<div class="math-block">$$\|H\|_2^2=\sum_{k=1}^{\infty}0.36(0.64)^{k-1}=\frac{0.36}{1-0.64}=1,\qquad \|H\|_2=1.$$</div>
<p>The controllability Gramian solves $W_c-0.64W_c=1$, hence $W_c=1/0.36=25/9$. Its output-energy formula gives $C^2W_c+D^2=(9/25)(25/9)=1$, exactly the same squared $\mathcal H_2$ norm. The displayed norms concern signals, not the norm of one state.</p>
<p><strong>(c)</strong> The nonnegative storage $V=1.8x^2$ has zero initial value. Expand its difference against the gain-$3$ supply:</p>
<div class="math-block">$$\begin{aligned}V(0.8x+w)-V(x)-9w^2+z^2&=1.8(0.64x^2+1.6xw+w^2)-1.8x^2-9w^2+0.36x^2\\&=-0.288x^2+2.88xw-7.2w^2\\&=-0.288(x-5w)^2\le0.\end{aligned}$$</div>
<p>Thus $V(x_{t+1})-V(x_t)\le9w_t^2-z_t^2$ at every step. Summing from $0$ to $T$ telescopes the storage terms:</p>
<div class="math-block">$$\sum_{t=0}^{T}z_t^2\le9\sum_{t=0}^{T}w_t^2+V(x_0)-V(x_{T+1})\le9\sum_{t=0}^{T}w_t^2.$$</div>
<p>Taking square roots proves gain at most $3$ on every finite horizon. It equals the exact $\mathcal H_\infty$ norm from (b), so this storage certificate is tight.</p>
''')

replace('exercise-41', 'State each theorem hypothesis, derive the frequency real-part minimum and strict margin, and distinguish nonlinear sector certification from constant-gain tests.', r'''
<p><strong>(a)</strong> Since $\tanh0=0$ and $|\tanh v|\le|v|$, the memoryless map $\phi(v)=\kappa\tanh v$ has signal gain at most $\kappa$ and is globally Lipschitz. Exercise D.6 gives stable linear-block gain $3$. The feedback has no algebraic feedthrough, so it is well posed. Small gain certifies $3\kappa\lt1$, namely $0\lt\kappa\lt1/3$. Equality supplies no strict small-gain certificate.</p>
<p><strong>(b)</strong> Tanh has the sign of its argument and magnitude at most that argument's magnitude, so $\phi$ lies in sector $[0,\kappa]$. Apply the stated negative-feedback circle criterion to the stable transfer $H(z)=0.6/(z-0.8)$. The one-state realization has nonzero input and output coefficients, so it is controllable and observable. Rationalizing the denominator on the unit circle gives</p>
<div class="math-block">$$\operatorname{Re}H(e^{j\omega})=\frac{0.6(\cos\omega-0.8)}{1.64-1.6\cos\omega}.$$</div>
<p>Set $r=\cos\omega\in[-1,1]$. The denominator is positive, and differentiation gives</p>
<div class="math-block">$$\frac{d}{dr}\frac{0.6(r-0.8)}{1.64-1.6r}=\frac{0.6[1.64-1.6r+1.6(r-0.8)]}{(1.64-1.6r)^2}=\frac{0.216}{(1.64-1.6r)^2}\gt0.$$</div>
<p>The minimum is therefore at $r=-1$ ($\omega=\pi$), where it equals $0.6(-1.8)/3.24=-1/3$. Consequently the frequency margin is $\min_\omega[1+\kappa\operatorname{Re}H]=1-\kappa/3$. It is strictly positive exactly for $0\lt\kappa\lt3$. For such $\kappa$ choose $\varepsilon=1-\kappa/3$ in the theorem; it certifies the sector loop, including this tanh feedback. At $\kappa=3$ that margin is zero.</p>
<p><strong>(c)</strong> For the constant law $\phi(v)=kv$, substitution gives $w=-0.6kx$ and $x_{t+1}=(0.8-0.6k)x_t$. Stability requires</p>
<div class="math-block">$$-1\lt0.8-0.6k\lt1\ \Longleftrightarrow\ -\frac13\lt k\lt3.$$</div>
<p>For nonnegative sector gains, every constant $k\in[0,\kappa]$ is stable precisely when $\kappa\lt3$, matching the circle certificate here. Checking constants alone is not a general nonlinear stability theorem; the circle criterion uses the sector inequality itself. Small gain ignores the helpful negative-feedback sign and certifies only $\kappa\lt1/3$, one ninth of this positive range. Failure of a sufficient test is not a proof of instability.</p>
''')

replace('exercise-42', 'Derive predecessor intervals and their exact limiting radii, prove maximality of the kernel, and show robust tube invariance and both tightened constraints.', r'''
<p><strong>(a)</strong> Starting with $X^0=K=[-1,1]$, suppose the current interval is $[-c,c]$. The possible next states from $x$ form $[1.5x-0.3,1.5x+0.3]$. This interval meets $[-c,c]$ exactly when $|1.5x|\le c+0.3$, so</p>
<div class="math-block">$$\operatorname{Pre}([-c,c])=\left[-\frac{c+0.3}{1.5},\frac{c+0.3}{1.5}\right],\qquad c_{k+1}=\min\left\{c_k,\frac{c_k+0.3}{1.5}\right\}.$$</div>
<p>The fixed radius is $c=0.6$. Since $c_0=1\gt0.6$, the predecessor radius is smaller than $c_k$ but remains above $0.6$, so that branch is selected at every finite iteration. Subtracting the fixed radius gives $c_{k+1}-0.6=(2/3)(c_k-0.6)$, hence</p>
<div class="math-block">$$c_k=0.6+0.4(2/3)^k:\quad1,\ 0.8666667,\ 0.7777778,\ 0.7185185,\ 0.6790123,\ldots\to0.6.$$</div>
<p>Every controlled invariant subset of $K$ must be contained in each backward feasible set, hence in their intersection $[-0.6,0.6]$. Conversely, on that interval $u=-0.5x$ has magnitude at most $0.3$ and gives next state $1.5x-0.5x=x$. This proves controlled invariance and establishes the full viability kernel $[-0.6,0.6]$.</p>
<p><strong>(b)</strong> Write the true and nominal states as $x_t=z_t+e_t$ and use $u_t=v_t+Ke_t$. Subtracting the nominal recursion $z_{t+1}=z_t+v_t$ from the true one gives $e_{t+1}=(1+K)e_t+w_t=0.4e_t+w_t$. With zero initial error and disturbance interval $W=[-0.2,0.2]$, the sum of scaled intervals has radius</p>
<div class="math-block">$$r=0.2\sum_{j=0}^{\infty}0.4^j=\frac{0.2}{1-0.4}=\frac13,\qquad E=[-1/3,1/3].$$</div>
<p>It is robustly invariant: if $|e_t|\le1/3$, then $|e_{t+1}|\le0.4/3+0.2=1/3$. The same proof also permits any $e_0\in E$. The state constraint needs room for every error, giving $z_t\in X\ominus E=[-2+1/3,2-1/3]=[-5/3,5/3]$.</p>
<p>Since multiplying the symmetric error interval by $K=-0.6$ gives $KE=[-0.2,0.2]$, the nominal input constraint is $v_t\in U\ominus KE=[-0.8,0.8]$. These tightened bounds imply $|x_t|\le5/3+1/3=2$ and $|u_t|\le0.8+0.2=1$ for every admitted disturbance sequence. They concern a feasible nominal plan and the stated uniform disturbance bound; the tube alone does not construct that plan.</p>
''')

retained = {
    'sys-ready-1': 'Already complete for the one-equation readiness task: forms the fixed-point equation, subtracts the state coefficient, obtains 2 and checks it by substitution; the discrete/continuous distinction is explained.',
    'sys-ready-2': 'Already adequate for a first-course calculus reader: gives the derivative -6e^{-2t}, rewrites it as -2x(t), supplies both initial values and explains state versus rate with units and the local update interpretation.',
    'sys-ready-3': 'Already computes the squared Euclidean length 5 and quadratic value 9, and explains why coefficients between 1 and 2 give the requested general sandwich inequality. No substantive intermediate operation is omitted.',
    'sys-extra-1': 'Already substitutes each indexed input into the newest state to obtain 2,1,-0.5, solves the constant-input fixed point 2, and explains why changing inputs leaves it. All requested steps and interpretation are present.',
    'sys-extra-2': 'Already substitutes feedback into the plant, obtains multiplier 0.25, solves the zero equilibrium and gives the exact repeated-update solution and first states. The convergence condition and changed closed-loop dynamics are explained.',
    'sys-extra-4': 'Already gives the coordinatewise exact trajectory, both requested states and the growing alternating coordinate. The magnitude-1.2 eigenvalue explicitly explains discrete-time instability and its distinction from continuous-time negative-real-part tests.',
    'sys-extra-5': 'Already solves both scalar ODEs, expands the squared norm, justifies e^{-4t}<=e^{-2t} for nonnegative time, and takes square roots to produce C=5. The exponential interpretation is complete.',
    'sys-extra-7': 'Already uses the chain rule to derive dot V=-4V, solves the certificate equation and gives its initial value x_0 squared. The square-root state decay explains the difference between the two exponents.',
    'sys-extra-13': 'Already derives the actual closed-loop coefficient and solution, identifies k>2 exactly, and explains the k=2 stable/non-attractive case and k<2 growth. All gain and boundary requests are covered.',
    'sys-extra-16': 'Already shifts by equilibrium 1/2, solves the resulting error equation using its initial value, obtains the full trajectory and compares its steady limit with G(0). The zero-state scope is explicit.',
    'sys-extra-17': 'Already derives the reciprocal complex modulus, evaluates both frequencies and identifies the maximum through the denominator. The stable-system energy-gain interpretation is provided. This elementary frequency calculation needs no further expansion.',
    'sys-extra-18': 'Already sums both geometric series, obtains l1=2 and l2=2/sqrt(3), proves the bounded-input convolution upper bound and supplies asymptotic attainment by a constant input. The impulse-energy versus induced-peak distinction answers the conceptual part.',
    'sys-extra-19': 'Already splits the input into unsaturated and saturated cases, checks both signs through v*sign(v)=|v|, and proves the all-input [0,1] sector. This short case proof is fully worked.',
    'sys-extra-21': 'Already differentiates x squared and uses the nonnegative sector product to prove exponential decay despite the failed norm-product test. Local Lipschitz uniqueness plus the bounded trajectory establishes forward existence, and the lost sign information explains the test gap.',
    'sys-extra-22': 'Already computes AB, forms the controllability matrix, checks rank 1 against state dimension 2 and explains directly why the second coordinate stays zero from zero. The distinction from stability is clear.',
    'sys-extra-23': 'Already computes the finite Gramian 2, derives the energy lower bound 1/2 from the integral endpoint constraint and Cauchy-Schwarz, and checks the constant attaining input. Both feasibility and optimality are proved.',
    'sys-extra-24': 'Already gives all transformed matrices, computes both transfer expressions and shows their equality. The commutation and invertible-coordinate requirement explain the calculation and its physical interpretation.',
    'sys-extra-25': 'Already substitutes dynamics, expands the quadratic, differentiates, checks the positive second derivative, and computes optimal input, next state and cost. The direct-to-zero comparison explains the effort tradeoff.',
}


if __name__ == '__main__':
    baseline = json.loads(BASE.read_bytes())
    decisions = []
    for exercise in baseline['exercises']:
        anchor = exercise['anchor'] or exercise['inventory_key'].split('::')[-1]
        if anchor in replacement:
            body = replacement[anchor]
            decision = 'replace'
            why = rationale[anchor]
        else:
            assert anchor in retained, 'Missing substantive assessment for ' + anchor
            body = exercise['solution']['html']
            decision = 'retain'
            why = retained[anchor]
        decisions.append({
            'inventory_key': exercise['inventory_key'],
            'source_file': exercise['source_file'],
            'authoring_file': exercise['authoring_file'],
            'ordinal': exercise['ordinal'],
            'label': exercise['label'],
            'original_solution_sha256': exercise['solution']['sha256'],
            'decision': decision,
            'thoroughness_rationale': why,
            'replacement_html': body,
            'selected_solution_sha256': sha256(body.encode()).hexdigest(),
        })
    assert len(decisions) == 42 and len(replacement) + len(retained) == 42
    result = {
        'schema_version': 1,
        'status': 'author_draft_requires_independent_math_depth_and_render_review',
        'author': 'solution_review_rotation',
        'page': 'SafeLearning/primer-systems.html',
        'baseline': {'file': str(BASE), 'sha256': sha256(BASE.read_bytes()).hexdigest()},
        'audience': 'First-course linear algebra and single-variable calculus; no earlier control course assumed.',
        'page_contract': {'file': 'page_contract.md', 'sha256': sha256(Path('page_contract.md').read_bytes()).hexdigest(), 'read_fully': True},
        'counts': {'exercises': 42, 'retain': len(retained), 'replace': len(replacement)},
        'exercises': decisions,
        'canonical_sources_or_coverage_records_edited': False,
        'new_citations': [],
    }
    with DEST.open('x', encoding='utf-8') as handle:
        json.dump(result, handle, indent=2, ensure_ascii=False)
        handle.write('\n')
    print(json.dumps({'file': str(DEST), 'sha256': sha256(DEST.read_bytes()).hexdigest(), 'counts': result['counts']}))
