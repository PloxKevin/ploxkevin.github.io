"""Complete the interrupted 65-exercise primer pass, preserving the v1 draft.

The first twelve proposals were authored before the crash. Further proposals
and retain rationales below are authored and reviewed by the recovery agent;
that review is not represented as an independent second-agent review.
"""
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'book/solutions'))
import solution_review as h

BASE = 'book/solutions/opening-step-review-v1'
old = runpy.run_path(str(ROOT / BASE / 'author_proposals_v1.py'))
replace, retain, decisions = old['replace'], old['retain'], old['DECISIONS']

replace('primer-basics', 16, 'Explain each image membership witness and both inclusions; injectivity identifies the two inputs in the reverse inclusion.', r'''
<p><strong>Compute the counterexample.</strong> The only member of $A$ is $-2$ and the only member of $B$ is $2$. They are distinct, so $A\cap B=\emptyset$. An image needs an input: no input in the empty set can produce an output, so $f(A\cap B)=\emptyset$. Separately, $f(-2)=(-2)^2=4$ and $f(2)=2^2=4$. Hence $f(A)=f(B)=\{4\}$ and $f(A)\cap f(B)=\{4\}$. The two sets differ because a common output need not come from a common input.</p>
<p><strong>First inclusion, for any function.</strong> Take any $y\in f(A\cap B)$. By the definition of image, there is an $x\in A\cap B$ with $f(x)=y$. Membership in the intersection means $x\in A$ and $x\in B$. The same input is a witness that $y\in f(A)$ and $y\in f(B)$. Thus $f(A\cap B)\subseteq f(A)\cap f(B)$.</p>
<p><strong>Reverse inclusion, using injectivity.</strong> Take any $y\in f(A)\cap f(B)$. Image membership supplies an $a\in A$ with $f(a)=y$ and a $b\in B$ with $f(b)=y$. Injectivity means equal outputs force equal inputs, so $a=b$. This one input belongs to both sets and maps to $y$, proving $y\in f(A\cap B)$. Both inclusions prove equality. In the counterexample the inputs $-2,2$ have equal outputs but differ, so precisely this injectivity step is unavailable.</p>
''')
replace('primer-basics', 17, 'List each successor before taking unions, prove stabilization and monotonicity by element membership, and exclude the disconnected cycle.', r'''
<p>Apply $F$ to each member of the <em>current</em> set, then retain the old members by taking a union. Starting with $S_0=\{0\}$,</p>
<div class="math-block">$$\begin{aligned}
F(S_0)&=\{F(0)\}=\{1\},&S_1&=\{0\}\cup\{1\}=\{0,1\},\\
F(S_1)&=\{F(0),F(1)\}=\{1,2\},&S_2&=\{0,1,2\},\\
F(S_2)&=\{1,2,2\}=\{1,2\},&S_3&=S_2.
\end{aligned}$$</div>
<p>A set lists repeated elements only once. Since $\Phi(S_2)=S_2$, this is a fixed point of the same operator. Applying it again gives $S_4=\Phi(S_3)=\Phi(S_2)=S_2$, and induction gives the same value forever. The final set is $\{0,1,2\}$, after two strict increases.</p>
<p>To prove monotonicity, assume $A\subseteq B$ and take any $y\in\Phi(A)$. Either $y\in A$, in which case $y\in B\subseteq\Phi(B)$, or $y=F(a)$ for some $a\in A$. Then $a\in B$, so $y\in F(B)\subseteq\Phi(B)$. Every member passes, proving $\Phi(A)\subseteq\Phi(B)$.</p>
<p>The map sends each of $0,1,2$ back into $\{0,1,2\}$. States $3,4$ map only to each other and neither is in the initial set. Induction therefore rules out adding either one. Monotonicity preserves previously added states; it does not make every disconnected state reachable.</p>
''')
replace('primer-basics', 18, 'Check every contraction hypothesis separately, solve fixed-point equations, and distinguish failure of a theorem hypothesis from failure of its conclusion.', r'''
<p>The theorem needs a nonempty closed subset of $\mathbb R$, a map into that same set, and a uniform distance factor strictly below $1$.</p>
<p><strong>(1) $X=(0,1]$, $g(x)=x/2$.</strong> For $0\lt x\le1$, $0\lt x/2\le1/2\le1$, so this is a self-map. Also $|g(x)-g(y)|=|x-y|/2$. Closedness fails: the members $1,1/2,1/4,\ldots$ approach $0$, which is excluded. A fixed point would satisfy $x=x/2$, so subtracting $x/2$ gives $x/2=0$, hence $x=0$. It is outside $X$, and no fixed point exists in $X$.</p>
<p><strong>(2) $X=[0,1]$, $g(x)=x/2+1$.</strong> The set is closed and the same subtraction shows contraction factor $1/2$. The self-map requirement fails: $g(1)=1/2+1=3/2\gt1$. Solving $x=x/2+1$ gives $x/2=1$, hence $x=2$, also outside $X$. No fixed point exists in the stated set.</p>
<p><strong>(3) $X=[-1,1]$, $g(x)=-x$.</strong> The set is closed, and changing the sign preserves membership. But $|g(x)-g(y)|=|x-y|$. For distinct inputs, dividing by their positive distance would require $1\le L$, so no contraction factor $L\lt1$ works. The fixed-point equation $x=-x$ gives $2x=0$, hence $x=0\in X$. From $x_0=1$, repeated sign changes give $1,-1,1,-1,\ldots$. Its even and odd subsequences have different limits, so the iteration does not converge.</p>
<p>Each failed assumption removes the theorem's guarantee. The explicit equations and trajectories determine what actually fails in these examples; a failed hypothesis alone would not decide that.</p>
''')
replace('primer-basics', 19, 'Expand the completed square and identify the equality case with an arbitrary-input argument.', r'''
<p>Take an arbitrary real number $x$. Expanding $(x+1)(x+1)$ gives $x^2+x+x+1=x^2+2x+1$. Thus</p>
<div class="math-block">$$x^2+2x+2=(x+1)^2+1\ge0+1=1.$$</div>
<p>The inequality holds because every real square is nonnegative. Equality occurs exactly when the added square is zero, which means $x+1=0$, hence $x=-1$. Substitution checks $(-1)^2+2(-1)+2=1-2+2=1$. No restriction was placed on $x$, so this proves the bound for every real input.</p>
''')
replace('primer-basics', 20, 'State the logical contrapositive before using integer parity and show the product expansion and integer witness.', r'''
<p>For integers, “not even” means odd. The contrapositive of “$n^2$ even implies $n$ even” is therefore “$n$ odd implies $n^2$ odd”. An implication and its contrapositive have the same truth value.</p>
<p>Assume $n$ is odd. By definition $n=2m+1$ for some integer $m$. Multiply out:</p>
<div class="math-block">$$\begin{aligned}
n^2&=(2m+1)(2m+1)\\
&=4m^2+2m+2m+1\\
&=4m^2+4m+1=2(2m^2+2m)+1.
\end{aligned}$$</div>
<p>The number $q=2m^2+2m$ is an integer because sums and products of integers are integers. Hence $n^2=2q+1$ is odd. This proves the contrapositive, and therefore the requested implication. We used the integer domain: even/odd classification would not apply to arbitrary real inputs.</p>
''')
replace('primer-basics', 21, 'Check the allowed inputs, premise and failing conclusion for each counterexample.', r'''
<p><strong>(1)</strong> Choose the real input $x=1/2$. Then $x^2=(1/2)(1/2)=1/4$, whereas $x=1/2=2/4$. Since $1/4\lt2/4$, the claimed $x^2\ge x$ fails.</p>
<p><strong>(2)</strong> Choose $x=0$, $y=1$. The premise holds: $xy=0(1)=0$. The conclusion demands both $x=0$ and $y=0$. Its second demand fails since $1\ne0$, so the implication is false at this permitted pair.</p>
<p><strong>(3)</strong> Choose $x=-1$, $y=1$. Their squares are $(-1)(-1)=1$ and $1(1)=1$, so the premise holds. The conclusion $x=y$ fails because $-1\ne1$.</p>
<p>A universal claim requires every allowed input to pass. One allowed input with a false conclusion refutes it. For an implication the premise must hold too; an example with a false premise would not refute that implication.</p>
''')
replace('primer-basics', 22, 'Expose the common denominator and factorization in the induction step and identify the exact next-index statement.', r'''
<p>Let $P(n)$ be the statement $\sum_{j=1}^n j=n(n+1)/2$.</p>
<p><strong>Base case.</strong> At $n=0$ the stipulated empty sum is $0$, and the right side is $0(0+1)/2=0$. Thus $P(0)$ holds.</p>
<p><strong>Induction hypothesis.</strong> Fix an integer $n\ge0$ and assume $P(n)$ is true. We must prove $P(n+1)$ from that assumption.</p>
<div class="math-block">$$\begin{aligned}
\sum_{j=1}^{n+1}j&=\sum_{j=1}^n j+(n+1)\\
&=\frac{n(n+1)}2+(n+1)\\
&=\frac{n(n+1)+2(n+1)}2\\
&=\frac{(n+1)(n+2)}2.
\end{aligned}$$</div>
<p>The first line separates the final term; the second uses the hypothesis; the third writes the added term over denominator $2$; the fourth factors out $n+1$. The resulting numerator is $(n+1)((n+1)+1)$, exactly the formula required by $P(n+1)$.</p>
<p><strong>Conclusion.</strong> The base case and step prove $P(n)$ for every integer $n\ge0$ by induction. The hypothesis concerns only index $n$; we did not assume the desired statement at $n+1$.</p>
''')
replace('primer-basics', 24, 'Derive the image bounds with order-preserving operations and show where the induction base uses the initial state.', r'''
<p><strong>One-step containment.</strong> Take any $x\in C=[0,1]$, so $0\le x\le1$. Dividing by the positive number $2$ preserves the order, and adding $1/4$ gives</p>
<div class="math-block">$$0\le x/2\le1/2
\quad\Longrightarrow\quad1/4\le x/2+1/4\le1/2+1/4=3/4.$$</div>
<p>Since $0\le1/4$ and $3/4\le1$, the successor lies in $[0,1]$.</p>
<p><strong>Induction.</strong> Let $P(t)$ mean $x_t\in C$. At $t=0$, $P(0)$ is exactly the given assumption $x_0\in C$. For the step, assume $P(t)$. The one-step argument is now applicable to $x=x_t$, and the recurrence gives $x_{t+1}=x_t/2+1/4\in C$. This proves $P(t+1)$. Induction gives membership at every integer time $t\ge0$.</p>
<p>The initial-state assumption supplies the base case. Without it, $x_0=2$ is permitted as a real number but outside $C$, and $x_1=2/2+1/4=5/4$ is still outside. One-step containment for points already in $C$ does not cover a start outside it.</p>
''')
replace('primer-basics', 25, 'Separate a conditional two-fixed-point argument from existence and verify all properties of the counterexample.', r'''
<p>Suppose there are two fixed points $a,b\in X$: $g(a)=a$ and $g(b)=b$. We prove they are the same. Put $d=|a-b|\ge0$. The given contraction inequality implies</p>
<div class="math-block">$$d=|g(a)-g(b)|\le d/3
\quad\Longrightarrow\quad d-d/3=2d/3\le0.$$</div>
<p>Multiplying by $3/2\gt0$ gives $d\le0$. Together with $d\ge0$, this forces $d=0$. Absolute value is zero only at zero, so $a-b=0$ and $a=b$. Thus there is <em>at most</em> one fixed point.</p>
<p>The proof starts by supposing fixed points exist; it does not produce one. For a counterexample to existence, take the nonempty set $X=(0,1]$ and $g(x)=x/3$. For $0\lt x\le1$, $0\lt x/3\le1/3\le1$, so this is a self-map. For all $x,y$, $|g(x)-g(y)|=|x-y|/3$, exactly the required bound. But $x=x/3$ gives $2x/3=0$, hence $x=0\notin X$. There is no fixed point. This set is not closed, so the existence part of the full contraction theorem is unavailable.</p>
''')
replace('primer-basics', 26, 'Keep membership and the quantitative estimate together in induction so the local hypothesis is available before it is applied.', r'''
<p>The proposed proof assumes all-time membership in order to apply a bound that is valid only inside $C$. That assumes its own conclusion.</p>
<p>Prove instead, by induction, both $x_t\in C$ and $|x_t|\le(4/5)^t|x_0|$. At $t=0$, membership is given, and the estimate is equality because $(4/5)^0=1$.</p>
<p>Assume both statements hold at index $t$. Membership in $C$ now justifies the bound on $F$ at the current state. Thus</p>
<div class="math-block">$$\begin{aligned}
|x_{t+1}|&=|F(x_t)|\le(4/5)|x_t|\\
&\le(4/5)(4/5)^t|x_0|=(4/5)^{t+1}|x_0|\le1.
\end{aligned}$$</div>
<p>The second inequality multiplies the induction estimate by a positive number. The last uses $|x_0|\le1$ and $0\lt(4/5)^{t+1}\le1$. The result proves both the next quantitative estimate and $x_{t+1}\in[-1,1]$. Induction gives both conclusions at all times. Future membership is derived after applying the valid current-state hypothesis.</p>
''')
replace('primer-basics', 27, 'Show the deterministic cycle and justify why the repeat found among five states excludes all new states after the first four; check the time-varying counterexample.', r'''
<p>Starting at $a$, successive substitutions give $x_0=a$, $x_1=F(a)=b$, $x_2=F(b)=c$, $x_3=F(c)=b$, and $x_4=F(b)=c$. From the repeated state $b$, the same fixed rule repeats $b,c,b,c,\ldots$. None of these states is $d$, so failure never occurs.</p>
<p>For a general fixed deterministic map on four states, consider the five states $x_0,\ldots,x_4$. The pigeonhole principle gives $x_i=x_j$ for some $0\le i\lt j\le4$. Applying the same function gives $x_{i+1}=F(x_i)=F(x_j)=x_{j+1}$. Induction on $m$ gives $x_{i+m}=x_{j+m}$ for every $m\ge0$.</p>
<p>Write the positive cycle length as $p=j-i$. From time $i$, states repeat with period $p$. For any $t\ge i$, division with remainder writes $t=i+qp+r$ with $0\le r\lt p$, so $x_t=x_{i+r}$. These cycle indices are at most $i+p-1=j-1\le3$. The initial prefix indices are smaller still. Hence every state ever visited appears among $x_0,\ldots,x_3$. Checking that prefix suffices to rule out a specified failure state.</p>
<p>For changing maps, let $F_t$ send every state to $a$ for $t=0,1,2$, and every state to $d$ for $t\ge3$. With $x_{t+1}=F_t(x_t)$ and $x_0=a$, the first four states are $a,a,a,a$, but $x_4=F_3(a)=d$. Equal states at different times need not have equal successors when different maps are used. The all-time conclusion needs the fixed deterministic rule.</p>
''')
replace('primer-basics', 28, 'Show all substitutions and positivity needed to rearrange the strict tolerance, then prove the integer cutoff and its minimality.', r'''
<p>Substitute $t=0,1,2,3$ into $a_t=3/(t+1)$: the first four terms are $3/1=3$, $3/2$, $3/3=1$, and $3/4$. Since $t+1$ grows without bound while the numerator stays $3$, the limit is $0$.</p>
<p>For $t\ge0$, $a_t\gt0$, so $|a_t|=a_t$. Both $t+1$ and $0.1$ are positive. Therefore</p>
<div class="math-block">$$\frac3{t+1}\lt0.1
\iff3\lt0.1(t+1)
\iff30\lt t+1
\iff29\lt t.$$</div>
<p>An integer greater than $29$ is at least $30$. For every $t\ge30$, $a_t\le3/31\lt1/10=0.1$; the strict comparison follows by cross-multiplying positive denominators: $30\lt31$. Thus $T=30$ works. At $t=29$, $a_{29}=3/30=0.1$, so the strict inequality fails. Any smaller threshold includes this failing index. Hence $30$ is the smallest threshold valid for every later term.</p>
''')

replace('primer-linalg', 1, 'State each norm definition, perform signed products and absolute values, and check the comparison without skipped arithmetic.', r'''
<p>For $x=(2,-1,2)^\top$ and $y=(1,2,0)^\top$, multiply corresponding coordinates and add:</p>
<div class="math-block">$$x^\top y=2(1)+(-1)(2)+2(0)=2-2+0=0.$$</div>
<p>Both vectors are nonzero, so this zero dot product means they are perpendicular in the standard Euclidean inner product.</p>
<p>The one-norm adds absolute coordinates, the two-norm takes the square root of their squared sum, and the infinity-norm takes the largest absolute coordinate:</p>
<div class="math-block">$$\begin{aligned}
\|x\|_1&=|2|+|-1|+|2|=2+1+2=5,\\
\|x\|_2&=\sqrt{2^2+(-1)^2+2^2}=\sqrt{4+1+4}=\sqrt9=3,\\
\|x\|_\infty&=\max\{2,1,2\}=2.
\end{aligned}$$</div>
<p>The negative coordinate contributes positively to every length. In three dimensions, the comparison is $\|x\|_\infty\le\|x\|_2\le\|x\|_1\le\sqrt3\|x\|_2$. Here it reads $2\le3\le5\le3\sqrt3$. For the last inequality both sides are nonnegative, so it is equivalent to $25\le27$. Norms measure size; the dot product also records relative direction.</p>
''')
replace('primer-linalg', 2, 'Prove both upper bounds and feasibility/attainment of the maximizing perturbations; explain the different balls.', r'''
<p>The objective is $w^\top\delta=3\delta_1-4\delta_2$ for $w=(3,-4)^\top$.</p>
<p><strong>Coordinatewise ball.</strong> The constraint $\|\delta\|_\infty\le0.2$ means $|\delta_1|,|\delta_2|\le0.2$. Hence</p>
<div class="math-block">$$3\delta_1-4\delta_2\le3|\delta_1|+4|\delta_2|
\le3(0.2)+4(0.2)=0.6+0.8=1.4.$$</div>
<p>Choose $\delta=(0.2,-0.2)^\top$. Its infinity-norm is $0.2$, and the objective is $3(0.2)-4(-0.2)=1.4$. An upper bound and a feasible attaining point prove the maximum is $1.4$.</p>
<p><strong>Euclidean ball.</strong> First $\|w\|_2=\sqrt{3^2+(-4)^2}=\sqrt{25}=5$. Cauchy–Schwarz gives $w^\top\delta\le|w^\top\delta|\le5\|\delta\|_2\le5(0.2)=1$. Choose the vector in the positive $w$ direction:</p>
<div class="math-block">$$\delta=\frac{0.2}{5}(3,-4)^\top=(0.12,-0.16)^\top.$$</div>
<p>It is feasible because $\|\delta\|_2=\sqrt{0.12^2+(-0.16)^2}=\sqrt{0.0144+0.0256}=\sqrt{0.04}=0.2$. Its objective is $3(0.12)-4(-0.16)=0.36+0.64=1$. Thus the Euclidean maximum is $1$.</p>
<p>The Euclidean ball lies inside the coordinatewise ball since each coordinate magnitude is at most the Euclidean norm. The box corner used above has Euclidean length $0.2\sqrt2\gt0.2$, so it is unavailable in the second problem. Equal numerical radii in different norms describe different perturbations.</p>
''')
replace('primer-optimization', 1, 'Differentiate each summand while holding the other coordinate constant, form every Hessian entry, and compute the finite vertical change.', r'''
<p>For $f(x_1,x_2)=x_1^2+x_1x_2+2x_2^2$, a partial derivative treats the other coordinate as constant. With respect to $x_1$, the three summands give $2x_1$, $x_2$ and $0$. With respect to $x_2$, they give $0$, $x_1$ and $4x_2$. Thus</p>
<div class="math-block">$$\nabla f(x_1,x_2)=(2x_1+x_2,\ x_1+4x_2)^\top.$$</div>
<p>Differentiate these two entries again. The first entry has derivatives $2,1$ and the second has derivatives $1,4$, so $\nabla^2f=\begin{bmatrix}2&1\\1&4\end{bmatrix}$. The mixed entries agree, as expected for this polynomial.</p>
<p>At $(1,-1)$, substitution gives $(2(1)-1,\ 1+4(-1))^\top=(1,-3)^\top$. In direction $v=(0,1)^\top$, the directional derivative is $\nabla f^\top v=1(0)+(-3)(1)=-3$.</p>
<p>To see its meaning, a vertical displacement $t$ gives $f(1,-1+t)=1+(-1+t)+2(-1+t)^2=2-3t+2t^2$. Subtracting $f(1,-1)=2$ leaves $-3t+2t^2$. The linear coefficient is the computed derivative; the quadratic remainder explains why it is a local slope rather than the exact change for a finite step.</p>
''')
replace('primer-optimization', 2, 'Show substitution, scalar derivatives, chain-rule velocities and the safety interpretation at the stated time.', r'''
<p>For $h(x)=1-x_1^2-x_2^2$ along $x(t)=(t,t^2)^\top$, substitute both coordinates: $h(x(t))=1-t^2-(t^2)^2=1-t^2-t^4$. The ordinary derivative is $-2t-4t^3$, which at $t=1$ equals $-2-4=-6$.</p>
<p>For the chain rule, the partial derivatives give $\nabla h(x)=(-2x_1,-2x_2)^\top$. Along this path they become $(-2t,-2t^2)^\top$. Differentiating the coordinates of the path gives $\dot x(t)=(1,2t)^\top$. Their dot product is</p>
<div class="math-block">$$\nabla h(x(t))^\top\dot x(t)=(-2t)(1)+(-2t^2)(2t)=-2t-4t^3.$$</div>
<p>The two methods agree because the chain rule differentiates exactly the same composition. At $t=1$, the state is $(1,1)^\top$ and $h=1-1-1=-1$. For safety defined by $h\ge0$, it is already outside the safe set; the negative derivative says its margin is decreasing locally. A derivative at one instant does not establish safety along the full path.</p>
''')
replace('primer-optimization', 3, 'Derive the gradient/Hessian and quadratic model, then show the third-derivative remainder and numerical comparison.', r'''
<p>For $f(x,y)=e^x+y^2$, the gradient is $(e^x,2y)^\top$ and the Hessian is $\operatorname{diag}(e^x,2)$. At $(0,0)$ these are $(1,0)^\top$ and $\operatorname{diag}(1,2)$, while $f(0,0)=1$. The quadratic Taylor model is</p>
<div class="math-block">$$m(x,y)=1+(1,0)(x,y)^\top+\tfrac12(x,y)\operatorname{diag}(1,2)(x,y)^\top
=1+x+\tfrac12(x^2+2y^2).$$</div>
<p>At $(0.1,0.2)$, $m=1+0.1+0.1^2/2+0.2^2=1+0.1+0.005+0.04=1.145$. The exact value is $e^{0.1}+0.04\approx1.145170918$.</p>
<p>The $y^2$ term is represented exactly, so only the scalar exponential has a remainder. Taylor's theorem gives $e^{0.1}=1+0.1+0.1^2/2+e^\xi(0.1)^3/6$ for some $0\lt\xi\lt0.1$. Since $0\lt e^\xi\le e^{0.1}$,</p>
<div class="math-block">$$0\le f-m\le\frac{e^{0.1}(0.1)^3}{6}\approx0.000184195.$$</div>
<p>The actual error is approximately $1.145170918-1.145=0.000170918$, below that bound. The Hessian term must carry the factor $1/2$; it is this factor that yields $x^2/2+y^2$. Decimal evaluations are approximations; the inequality with $e^{0.1}/6000$ is the exact certificate.</p>
''')
replace('primer-systems', 2, 'Apply the scalar chain rule explicitly, substitute time zero, and distinguish state units from rate units.', r'''
<p>For $x(t)=3e^{-2t}$, the chain rule multiplies the exponential by the derivative of its exponent:</p>
<div class="math-block">$$\dot x(t)=3e^{-2t}\frac{d(-2t)}{dt}=3e^{-2t}(-2)=-6e^{-2t}=-2x(t).$$</div>
<p>At $t=0$, $e^0=1$, so $x(0)=3$ and $\dot x(0)=-6$. The first is a state value; the second is its rate of change. For example, metres and metres per second are different units.</p>
<p>Over a small positive time interval $\Delta t$, the first-order approximation is $x(\Delta t)\approx3-6\Delta t$. A negative rate says that the state is initially decreasing; it does not say that the state itself equals $-6$. At a general time, $x(t+\Delta t)\approx x(t)+\Delta t\dot x(t)$.</p>
''')
replace('primer-systems', 3, 'Show both matrix products and prove both comparison inequalities for an arbitrary vector by nonnegative differences.', r'''
<p>With $x=(1,-2)^\top$ and $P=\operatorname{diag}(1,2)$, the Euclidean squared length is $x^\top x=1^2+(-2)^2=1+4=5$. First multiply $Px=(1,-4)^\top$, then</p>
<div class="math-block">$$V=x^\top Px=(1,-2)(1,-4)^\top=1(1)+(-2)(-4)=1+8=9.$$</div>
<p>For any vector $z=(z_1,z_2)^\top$, $V(z)=z_1^2+2z_2^2$. Subtracting the proposed lower and upper comparisons gives</p>
<div class="math-block">$$V(z)-\|z\|_2^2=z_2^2\ge0,\qquad
2\|z\|_2^2-V(z)=z_1^2\ge0.$$</div>
<p>Thus $\|z\|_2^2\le V(z)\le2\|z\|_2^2$ for every vector. At the given point this reads $5\le9\le10$. In particular, an upper bound $V(z)\le B$ with $B\ge0$ implies $\|z\|_2\le\sqrt B$. This is how a quadratic certificate bounds physical state size; its value is not simply the state vector itself.</p>
''')
replace('primer-rl-nn', 2, 'Derive the finite geometric sum by subtraction, including the zero-term case, before taking its limit.', r'''
<p>The reward at time $t$ is $2$ and its discount weight is $(1/2)^t$, so the first terms are $2,1,1/2,1/4,\ldots$. For $T\ge1$, let $S_T=1+1/2+\cdots+(1/2)^{T-1}$. Then $S_T/2=1/2+\cdots+(1/2)^T$. Subtracting cancels the common terms:</p>
<div class="math-block">$$S_T-S_T/2=1-2^{-T},\qquad S_T=2(1-2^{-T}).$$</div>
<p>Multiplying by the reward $2$ gives the discounted partial return $2S_T=4(1-2^{-T})$. The same formula gives zero for $T=0$, consistent with an empty sum. Since $2^{-T}\to0$, the infinite return is $4$. This also equals $2/(1-1/2)$ by the geometric-series formula.</p>
<p>Without discounting, $T$ rewards of $2$ would sum to $2T$, which grows without bound. The finite infinite-horizon value here depends on the discount ratio being strictly below $1$.</p>
''')
replace('primer-rl-nn', 3, 'Evaluate the linear model and use exact perturbations to explain the two partial derivatives and what is held fixed.', r'''
<p>For $f_\theta(x)=\theta x$, with $\theta=3$ and $x=2$, the output is $3(2)=6$. A partial derivative changes one argument while holding the other fixed.</p>
<p>Hold the input at $2$ and change the parameter by $\Delta\theta$. Then $f_{3+\Delta\theta}(2)=6+2\Delta\theta$. Dividing its change by $\Delta\theta\ne0$ gives $2$, so $\partial f/\partial\theta=x=2$.</p>
<p>Hold the parameter at $3$ and change the input by $\Delta x$. Then $f_3(2+\Delta x)=6+3\Delta x$. Dividing by $\Delta x\ne0$ gives $3$, so $\partial f/\partial x=\theta=3$.</p>
<p>The first derivative describes how a parameter update changes the output at this input. The second describes sensitivity to an input change for this fixed model. Backpropagation can compute both, but they answer different questions. Because this model is linear in each argument separately, these single-argument changes are exact, rather than merely first-order approximations.</p>
''')

RETAINS = {
13: 'Derives both image inclusions with a square-root witness, splits both preimage sign branches, includes endpoints and explains the lack of an inverse.',
14: 'Checks injectivity and surjectivity independently for all four domains/codomains, factors equal squares, and verifies both inverse compositions.',
15: 'Solves the fixed point, computes three iterates, derives the signed and absolute error recurrence, and proves the minimal integer using adjacent powers.',
23: 'Checks both erroneous negative-multiplier operations and repairs them with nonnegative factors, including equality and a factorization check.',
29: 'Proves absolute convergence, computes all four terms, derives the tail bound and uses an attaining reward sequence to prove the cutoff minimal.',
30: 'Writes telescoping cancellation, derives energy convergence and the global excursion count, then gives a compatible arbitrarily late excursion.',
31: 'Distinguishes bounds from attained extrema, supplies approaching sequences and smaller/larger members, and proves each supremum/infimum.',
32: 'Separates parity, checks attained bounds, and applies the tail definitions of limsup and liminf to explain nonconvergence.',
33: 'Computes each row maximum and column minimum explicitly and explains the response order and minimax gap.',
34: 'Constructs interior and exterior neighborhoods, an endpoint-approaching sequence, and checks closedness/boundedness before compactness.',
35: 'Supplies a minimizing sequence or attained lower bound in every domain, and separates the extreme value theorem from explicit existence.',
36: 'Derives nearest-grid distances, transfers the Lipschitz bound, and proves the coarse-grid counterexample is Lipschitz and meets every measurement.',
37: 'Gives explicit upper/lower constants and the threshold, and tests the little-o limit separately.',
38: 'Solves each positive-denominator tolerance and multiplies the resulting iteration counts by the stated operation cost; compares sufficient budgets.',
39: 'Divides cumulative regret by time, differentiates the limit ratio, evaluates the finite bound and verifies the product counterexample.',
40: 'Derives the information interval, checks both reading endpoints and acceptance boundaries, and supplies safe and unsafe compatible states.',
41: 'Derives the full disturbance interval, intersects the actuator bounds, verifies the command and exposes the incompatible quantifier order.',
42: 'Derives the affine error envelope by induction, supplies an equality witness for impossibility and distinguishes strict/non-strict integer cutoffs.',
43: 'Proves necessity at the boundary and sufficiency with an explicit legal feedback, checks all disturbances and extends the argument by induction.',
44: 'Negates both quantifiers, checks the feedback witness and actuator interval, and derives the conflicting shared-input endpoint inequalities.',
45: 'Computes each witness radius and set round, proves stabilization, counts increases and evaluates the two failed gateway links.',
46: 'Shows the induction denominator/cancellation steps, justifies exchanging nonnegative sums, and interprets normalized discount weights as a law.',
47: 'Checks attained and unattained bounds, parity limits, the trigonometric common-input maximum and both inner response sign cases.',
48: 'Treats each existence case with a lower bound and witness, derives the constrained norm identity and splits every sublevel parameter case.',
49: 'Verifies limiting ratios, differentiates the eventual tolerance bound, checks adjacent integer cutoffs and multiplies grid/dimension costs.',
50: 'Checks all contraction hypotheses, reverses the logarithmic inequality correctly and distinguishes global bounds from certified interval iteration.',
}
for ordinal, rationale in RETAINS.items():
    retain('primer-basics', ordinal, rationale)
retain('primer-linalg', 3, 'Explains the epsilon witness from an infimum, both triangle inequalities, an attaining disc point, and the displacement interval without assuming a nearest point exists.')
retain('primer-probability', 1, 'Defines the complement, uses disjoint probabilities summing to one and interprets the event without claiming a trajectory-wide bound.')
retain('primer-probability', 2, 'Lists four equally weighted representative values, computes their average and gives the equivalent probability-weighted expression.')
retain('primer-probability', 3, 'Multiplies every outer-product entry, expands the arbitrary-vector quadratic form and gives a nonzero null-vector witness.')
retain('primer-systems', 1, 'Writes and solves the equilibrium equation, checks substitution and distinguishes continuous-time equilibrium.')
retain('primer-rl-nn', 1, 'Calculates the weighted reward, separates the two possible outcomes from their mean and explains what a policy specifies.')


def main():
    snapshot = h.read(BASE + '/current-source-v1.json')
    assert len(snapshot['exercises']) == len(decisions) == 65
    rows = []
    for row in snapshot['exercises']:
        key = (Path(row['source_file']).name, row['ordinal'])
        d = decisions[key]
        rows.append({'inventory_key': row['inventory_key'], 'source_file': row['source_file'],
                     'ordinal': row['ordinal'], 'authoring_file': row['author_file'],
                     'original_solution_sha256': row['parts']['solution']['sha256'], **d,
                     'author': '/root/solution_review_rotation' if key[0] == 'primer-basics.html' and key[1] <= 12 else '/root',
                     'review_mode': 'independent_recovery_review' if key[0] == 'primer-basics.html' and key[1] <= 12 else 'recovery_author_self_review_or_exact_prior_retain'})
    assert sum(r['decision'] == 'replace' for r in rows) == 33
    h.json_put(BASE + '/assessments-v2.json', {'status': 'completed65_primer_opening_assessments',
        'source_version': 'Source91', 'source_snapshot': h.ref(BASE + '/current-source-v1.json'),
        'author_helpers': [h.ref(BASE + '/author_proposals_v1.py'), h.ref(BASE + '/author_proposals_v2.py')],
        'counts': {'exercises': 65, 'replace': 33, 'retain': 32}, 'exercises': rows,
        'independent_review_of_recovery_authored_changes_claimed': False,
        'scope': 'All 50 Primer0 exercises and the first three actual DOM exercises of each other primer. Exact prior reviewed retained bodies remain unchanged.'})
    print({'exercises': 65, 'replace': 33, 'retain': 32})


if __name__ == '__main__':
    main()
