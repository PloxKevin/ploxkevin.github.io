"""Prepare fifty individual solution decisions; write draft artifacts only."""
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[3]
BASELINE = 'book/solutions/baseline-source90/pages/primer-basics.html.json'
OUT = 'book/solutions/drafts/primer-basics-thorough-solutions-v1.json'
page = json.loads((ROOT / BASELINE).read_bytes())
assert len(page['exercises']) == 50


def ref(file):
    return {'file': file, 'sha256': sha256((ROOT / file).read_bytes()).hexdigest()}


def body(text):
    return '\n' + text.strip() + '\n'


replacements = {}
rationales = {}


def replace(ordinal, rationale, html):
    assert ordinal not in replacements
    replacements[ordinal] = body(html)
    rationales[ordinal] = rationale


replace(13, 'Make the image calculation a two-inclusion argument and explain the two sign branches in the preimage. Distinguish a preimage set from an inverse by actual repeated and missing outputs.', r'''
<p><strong>Image: start with the permitted inputs.</strong> The notation $f([-3,1])$ asks for all squares of numbers in $[-3,1]$. Every such input has $|x|\le3$, so $0\le x^2\le9$. This proves that no output lies outside $[0,9]$. To show that none of the values inside is missing, take any $y\in[0,9]$ and choose $x=-\sqrt y$. Then $-3\le x\le0$, so this input is permitted, and $f(x)=(-\sqrt y)^2=y$. Therefore $f([-3,1])=[0,9]$.</p>
<p><strong>Preimage: start with the required outputs.</strong> Here the domain is all of $\mathbb R$, and $f^{-1}([1,4])$ asks which real inputs have square between $1$ and $4$. Taking nonnegative square roots gives</p>
<div class="math-block">$$1\le x^2\le4\quad\Longleftrightarrow\quad1\le|x|\le2.$$</div>
<p>If $x\ge0$, this condition gives $1\le x\le2$. If $x\lt0$, use $|x|=-x$ to obtain $1\le-x\le2$, or $-2\le x\le-1$. Both branches are needed, so $f^{-1}([1,4])=[-2,-1]\cup[1,2]$. All four endpoints are included because the output inequalities allow equality.</p>
<p><strong>Test the negative output separately.</strong> A real square is always nonnegative, so there is no real $x$ with $x^2=-1$. Consequently $f^{-1}(\{-1\})=\emptyset$.</p>
<p><strong>Interpret the notation.</strong> A preimage means “collect every input whose output passes this test”; it may contain several inputs or none. It does not require an inverse function. An inverse would assign exactly one input to each output in the codomain. Squaring on $\mathbb R$ fails that requirement: $-1$ and $1$ both give $1$, and no input gives $-1$.</p>
''')

replace(14, 'Restate injectivity and surjectivity as concrete tests, prove nonnegative-input uniqueness by factorization, and check both inverse identities for the fourth map.', r'''
<p><strong>Use two separate tests.</strong> Injectivity asks whether different permitted inputs can give the same output. Surjectivity asks whether every element of the declared codomain is actually reached. The formula is the same in all four cases, but the permitted inputs and required outputs change.</p>
<ol>
<li><p><strong>$\mathbb R\to\mathbb R$: neither.</strong> The distinct inputs $-1$ and $1$ both have square $1$, so the map is not injective. The codomain contains $-1$, but every real square is nonnegative, so $-1$ is never reached. Thus it is not surjective either.</p></li>
<li><p><strong>$\mathbb R\to[0,\infty)$: surjective only.</strong> Given any required output $y\ge0$, the real input $x=\sqrt y$ satisfies $x^2=y$. This supplies an input for every element of this smaller codomain. The inputs $-1$ and $1$ are still permitted, so the failure of injectivity remains.</p></li>
<li><p><strong>$[0,\infty)\to\mathbb R$: injective only.</strong> Suppose $x,x'\ge0$ and $x^2=(x')^2$. Factoring gives $(x-x')(x+x')=0$. Either $x=x'$, or $x+x'=0$; in the second case nonnegativity forces $x=x'=0$. Thus the inputs are equal in every case. However, the codomain is still all of $\mathbb R$, and negative outputs remain impossible, so the map is not surjective.</p></li>
<li><p><strong>$[0,\infty)\to[0,\infty)$: both.</strong> The uniqueness argument from (3) proves injectivity, and the input $x=\sqrt y$ from (2) proves surjectivity for every $y$ in this codomain. This map is therefore bijective.</p></li>
</ol>
<p>The inverse of the bijective map is $f^{-1}(y)=\sqrt y$ for $y\ge0$. Check both directions: $(\sqrt y)^2=y$, and $\sqrt{x^2}=x$ when $x\ge0$. The last identity would be $|x|$ on all of $\mathbb R$, which explains why restricting the domain matters.</p>
''')

replace(15, 'Show the fixed-point algebra, every substitution, the signed-error recurrence and its iteration; convert the error target into a power-of-two condition before checking minimality.', r'''
<p><strong>Find the point that stays fixed.</strong> Set the output equal to the input and solve:</p>
<div class="math-block">$$x^\ast=-\frac{x^\ast}{2}+3
 \quad\Longrightarrow\quad\frac32x^\ast=3
 \quad\Longrightarrow\quad x^\ast=2.$$</div>
<p><strong>Iterate from the stated start.</strong> Each new value is obtained by putting the previous value into $g$:</p>
<div class="math-block">$$\begin{aligned}
x_1&=-0/2+3=3,\\
x_2&=-3/2+3=3/2,\\
x_3&=-(3/2)/2+3=-3/4+3=9/4.
\end{aligned}$$</div>
<p><strong>Check the contraction for every pair.</strong> For arbitrary real $x,y$, the constant terms cancel, giving $g(x)-g(y)=-(x-y)/2$. Taking absolute values gives $|g(x)-g(y)|=\tfrac12|x-y|$. Since $1/2\lt1$, this is a contraction on $\mathbb R$ with factor $1/2$.</p>
<p><strong>Compute the exact error.</strong> Subtract the fixed-point equation from the recurrence:</p>
<div class="math-block">$$\begin{aligned}
x_{k+1}-2&=-\tfrac12(x_k-2),\\
x_k-2&=(-\tfrac12)^k(x_0-2)=-2(-\tfrac12)^k,\\
|x_k-2|&=2(1/2)^k.
\end{aligned}$$</div>
<p>The second line follows by applying the first line $k$ times; at $k=0$ it is the initial error $-2$. The minus sign makes the signed error alternate, while its absolute size halves.</p>
<p><strong>Solve the tolerance and check the first integer.</strong> The requirement $2/2^k\le1/100$ is equivalent to $2^k\ge200$, since all denominators are positive. Now $2^7=128\lt200$ and $2^8=256\ge200$. Hence the smallest qualifying iteration is $k=8$. Directly, the errors are $1/64\gt1/100$ at $7$ and $1/128\lt1/100$ at $8$. Because these exact errors decrease, every earlier iteration also fails.</p>
''')

replace(23, 'Expose both wrongly oriented inequalities numerically, then repair the original two-step chain using the sign of each multiplier and also verify the factorization route.', r'''
<p><strong>Locate the unsupported step.</strong> Multiplication preserves $a\le b$ only for a nonnegative multiplier. The premise $a\le b$ does not tell us that either $a$ or $b$ is nonnegative. If a multiplier is negative, the inequality reverses.</p>
<p><strong>Check a counterexample through the actual operations.</strong> Take $a=-3$ and $b=-2$. The premise $-3\le-2$ is true. Multiplying it by $a=-3$ gives $9\ge6$, and multiplying it by $b=-2$ gives $6\ge4$. The proposed proof incorrectly writes the opposite directions. Its final claim would be $a^2\le b^2$, or $9\le4$, which is false.</p>
<p><strong>Repair the chain with the added hypothesis.</strong> Under $0\le a\le b$, both multipliers are now nonnegative. Multiplying $a\le b$ by $a$ gives $a^2\le ab$; multiplying the same inequality by $b$ gives $ab\le b^2$. Combining them yields $a^2\le ab\le b^2$. Zero multipliers are allowed: multiplication by zero simply gives equality.</p>
<p>You can check the same conclusion in one factorization: $b^2-a^2=(b-a)(b+a)$. The hypothesis gives $b-a\ge0$ and $b+a\ge0$, so their product is nonnegative. Therefore $b^2-a^2\ge0$, which is exactly $a^2\le b^2$. The sign assumption is what makes either repair valid.</p>
''')

replace(29, 'Explain why the geometric absolute bound also establishes convergence, display all discounted terms and the tail index, and use an attaining reward sequence to justify the smallest universal budget.', r'''
<p><strong>Bound the return before computing any particular sequence.</strong> Since $|r_t|\le2$ and the discount is $\gamma=1/2$, each discounted reward satisfies $|2^{-t}r_t|\le2\cdot2^{-t}$. The geometric series on the right converges, so the return converges absolutely. Applying the triangle inequality and summing gives</p>
<div class="math-block">$$\left|\sum_{t=0}^{\infty}2^{-t}r_t\right|
 \le\sum_{t=0}^{\infty}2^{-t}|r_t|
 \le2\sum_{t=0}^{\infty}(1/2)^t
 =\frac{2}{1-1/2}=4.$$</div>
<p><strong>Compute the four-term example.</strong> With $r_t=2$ at every time, the terms at $t=0,1,2,3$ are $2,1,1/2,1/4$. Their sum is $2+1+1/2+1/4=15/4=3.75$. The infinite sum is exactly $4$, so the omitted tail is $4-15/4=1/4$. Its first omitted term is at $t=4$, not at $t=3$.</p>
<p><strong>Keep the unknown rewards in the tail bound.</strong> After $T$ terms, the tail starts at $t=T$. For every allowed sequence,</p>
<div class="math-block">$$\left|\sum_{t=T}^{\infty}2^{-t}r_t\right|
 \le2\sum_{t=T}^{\infty}(1/2)^t
 =\frac{2(1/2)^T}{1-1/2}
 =4\cdot2^{-T}.$$</div>
<p>To guarantee a tail at most $0.01=1/100$, solve $4/2^T\le1/100$, equivalently $2^T\ge400$. The neighbouring powers are $2^8=256$ and $2^9=512$, so $T=9$ is sufficient. The corresponding bounds are $4/256=0.015625$ at $8$ and $4/512=0.0078125$ at $9$.</p>
<p>These checks also prove minimality for a guarantee about every reward sequence: the permitted sequence $r_t=2$ attains the tail bound. It therefore really has too much omitted return at $T=8$, and at every smaller $T$. The tolerance is an absolute return error, not a percentage of the infinite return.</p>
''')

replace(30, 'Write the telescoping cancellations and explain why bounded nonnegative partial sums yield vanishing squared norms. Make the all-time excursion count rigorous and exhibit a compatible arbitrarily late excursion.', r'''
<p><strong>Sum the one-step inequality.</strong> Add it for $t=0,\ldots,T-1$. The left side is</p>
<div class="math-block">$$(V_1-V_0)+(V_2-V_1)+\cdots+(V_T-V_{T-1})=V_T-V_0,$$</div>
<p>because each intermediate value appears once with each sign. Thus $V_T-V_0\le-\tfrac12\sum_{t=0}^{T-1}\|x_t\|^2$. Rearranging and using $V_T\ge0$, $V_0=3$, gives</p>
<div class="math-block">$$\frac12\sum_{t=0}^{T-1}\|x_t\|^2
 \le V_0-V_T\le3,
 \qquad
 \sum_{t=0}^{T-1}\|x_t\|^2\le6.$$</div>
<p><strong>Turn the energy budget into convergence.</strong> These partial sums increase because every squared norm is nonnegative, and they are bounded above by $6$. They therefore converge to a finite limit. If $S_T$ denotes the partial sum, then $\|x_T\|^2=S_{T+1}-S_T\to0$. Since the norms are nonnegative, taking square roots gives $\|x_T\|\to0$, which is the definition of $x_T\to0$.</p>
<p><strong>Count all excursions, not just an initial block.</strong> Whenever $\|x_t\|\ge0.2$, its squared norm is at least $(0.2)^2=0.04$. If $N$ such indices occur before a horizon $T$, then $0.04N\le\sum_{t=0}^{T-1}\|x_t\|^2\le6$, so $N\le150$. If there were $151$ excursions over all time, some finite horizon would contain all of the first $151$, contradicting that bound. There are therefore at most $150$ altogether.</p>
<p><strong>Distinguish existence of a last excursion from knowing its time.</strong> A finite set of excursion indices has a last member, so the stated assumptions imply an eventual absence of excursions. They do not supply a numerical time valid for every compatible sequence. For example, choose any large index $M$ and, in the scalar case, set $x_M=0.2$ and all other $x_t=0$. Keep $V_t=3$ through $t=M$, and set $V_t=2.98$ afterwards. At $M$, the decrease is $-0.02=-\tfrac12(0.2)^2$; at other times it is $0$. All assumptions hold, but the single excursion can occur as late as we choose. A time estimate requires additional information.</p>
''')

replace(31, 'Explain bounds versus attained extrema using actual witness sequences for the interval and an explicitly larger next element for the sequence set.', r'''
<p><strong>Separate two questions.</strong> An infimum or supremum is the tightest lower or upper bound. A minimum or maximum also has to belong to the set. We first find the bounds, then check whether they are attained.</p>
<p><strong>For $A=(-2,3]$.</strong> Every member satisfies $-2\lt x\le3$, so $-2$ is a lower bound and $3$ an upper bound. The values $-2+1/n$ belong to $A$ and tend to $-2$: any proposed lower bound larger than $-2$ eventually exceeds one of them and fails. Hence $\inf A=-2$. This value is excluded by the round bracket, so there is no minimum. Indeed, for any $x\in A$, the midpoint $(x-2)/2$ between $-2$ and $x$ is a smaller member of $A$.</p>
<p>The value $3$ belongs to $A$ and bounds every other member, so both $\sup A$ and $\max A$ equal $3$.</p>
<p><strong>For $B=\{1-1/n:n=1,2,\ldots\}$.</strong> Its first values are $0,1/2,2/3,3/4,\ldots$. For every $n\ge1$, we have $1/n\le1$, so $1-1/n\ge0$. At $n=1$ this value is $0$. Therefore $\inf B=\min B=0$.</p>
<p>Each $1-1/n$ is strictly less than $1$, so $1$ is an upper bound. To show it is the least one, take any $\varepsilon\gt0$ and choose an integer $n\gt1/\varepsilon$. Then $1/n\lt\varepsilon$ and $1-1/n\gt1-\varepsilon$: elements approach the proposed ceiling arbitrarily closely. Thus $\sup B=1$. No finite $n$ gives $1$, and $1-1/(n+1)\gt1-1/n$ always supplies a larger member. Consequently $B$ has no maximum.</p>
''')

replace(32, 'Expose the parity split and tail-supremum logic, rather than inferring limsup and liminf from unexplained subsequence limits.', r'''
<p><strong>Split the indices by parity.</strong> The sign $(-1)^t$ is $1$ for even $t$ and $-1$ for odd $t$. Hence</p>
<div class="math-block">$$a_{2k}=1+\frac1{2k+1},
 \qquad
 a_{2k+1}=-1+\frac1{2k+2},
 \qquad k=0,1,2,\ldots.$$</div>
<p>The even terms decrease from $a_0=2$ towards $1$. None exceeds $2$, and the odd terms are negative, so $\sup_ta_t=2$. It is attained at $t=0$ and is also the maximum.</p>
<p>The odd terms begin at $a_1=-1/2$ and decrease towards $-1$, staying strictly above $-1$ because their added fraction is positive. Even terms exceed $1$, so $-1$ bounds the whole sequence from below. Odd terms get arbitrarily close to it, proving $\inf_ta_t=-1$. No term equals $-1$, so no minimum exists.</p>
<p><strong>Now discard the finite beginning.</strong> For any index $T$, its tail still contains both parities. The largest tail value is the first even term whose index is at least $T$: later even terms are smaller, and all odd terms are negative. As $T$ increases, this largest tail value tends to $1$. By the definition $\limsup_ta_t=\lim_{T\to\infty}\sup_{t\ge T}a_t$, we obtain $\limsup_ta_t=1$.</p>
<p>The infimum of every tail is $-1$, since the remaining odd terms still approach $-1$ from above. Therefore $\liminf_ta_t=-1$. These two tail limits differ, so the sequence does not converge. The initial value $2$ changes the supremum over the entire sequence but disappears from sufficiently late tails; this is why the supremum and limit superior are different.</p>
''')

replace(34, 'Give explicit interior radii and missing-limit sequences, compute the boundary from definitions, and explain why the two-point set is compact without having any interior.', r'''
<p><strong>Interior: find room on both sides.</strong> If $-1\lt x\lt1$, the positive radius $r=\tfrac12\min\{x+1,1-x\}$ makes $(x-r,x+r)$ lie inside $(-1,1]$. Thus every such $x$ is interior. The point $1$ is in $A$, but every interval around it contains a number greater than $1$, outside $A$. It is not interior. No point outside $A$ is interior either, so $\operatorname{Int}A=(-1,1)$.</p>
<p><strong>Closure: include the possible limits.</strong> The missing endpoint $-1$ is a limit of members: $x_n=-1+1/n\in A$ and $x_n\to-1$. The other endpoint $1$ is already included. There are no limits outside $[-1,1]$, because every member is between these two bounds and inequalities persist under limits. Therefore $\operatorname{cl}A=[-1,1]$.</p>
<p><strong>Boundary: remove the interior from the closure.</strong> This gives $\partial A=[-1,1]\setminus(-1,1)=\{-1,1\}$. Every neighbourhood of either endpoint meets both $A$ and its complement. Only $1$ belongs to $A$, showing that a boundary point need not be a member of the original set.</p>
<p><strong>Classify $A$.</strong> It is not open, since its member $1$ is not interior. It is not closed, since the sequence above converges to the excluded point $-1$. It is bounded, for example by $|x|\le1$. In $\mathbb R$, the compact sets are exactly those that are closed and bounded. Hence $A$ is not compact.</p>
<p><strong>Check $B=\{0,1\}$ separately.</strong> It is bounded. It is closed: if $x$ is outside $B$, the radius $\tfrac12\min\{|x|,|x-1|\}\gt0$ gives an interval around $x$ avoiding both members, so the complement of $B$ is open. Thus $B$ is closed and bounded, and therefore compact. Neither $0$ nor $1$ has an interval around it inside $B$, so compactness here does not require interior points.</p>
''')

replace(36, 'Work through nearest-grid coverage, both inequality directions proving distance is Lipschitz, and the explicit unsafe coarse-grid counterexample.', r'''
<p><strong>Locate an arbitrary point relative to the fine grid.</strong> Adjacent points of $G=\{0,0.2,0.4,0.6,0.8,1\}$ are separated by $0.2$. Every $x\in[0,1]$ lies between two adjacent grid points or equals one. In a gap of length $0.2$, at least one endpoint is at distance at most $0.1$: the largest nearest-endpoint distance occurs at its midpoint. Choose such a grid point $g$.</p>
<p><strong>Transfer the measured lower bound.</strong> The Lipschitz assumption says $|h(x)-h(g)|\le3|x-g|$. Its lower side gives $h(x)-h(g)\ge-3|x-g|$, so</p>
<div class="math-block">$$h(x)\ge h(g)-3|x-g|
 \ge0.35-3(0.1)
 =0.05.$$</div>
<p>Since $x$ was arbitrary, $0.05$ is a uniform positive margin on the entire interval, including points that were not measured.</p>
<p><strong>Recompute coverage for the coarse grid.</strong> For $G_c=\{0,0.4,0.8,1\}$, the gaps are $0.4,0.4,0.2$. The largest nearest-grid distance is therefore $0.2$. The same reasoning now yields only $h(x)\ge0.35-3(0.2)=-0.25$. A negative lower bound does not itself prove a negative true value, so this calculation alone is not a counterexample.</p>
<p><strong>Construct one function showing failure is possible.</strong> Define $d_c(x)=\operatorname{dist}(x,G_c)=\min_{g\in G_c}|x-g|$, and set $h_c(x)=0.35-3d_c(x)$. A minimum exists because this grid is finite and nonempty. To check the required Lipschitz property, choose a nearest grid point $g_y$ for $y$. The triangle inequality gives</p>
<div class="math-block">$$d_c(x)\le|x-g_y|
 \le|x-y|+|y-g_y|
 =|x-y|+d_c(y).$$</div>
<p>Thus $d_c(x)-d_c(y)\le|x-y|$. Swapping $x,y$ gives the reverse bound, so $|d_c(x)-d_c(y)|\le|x-y|$. Consequently $|h_c(x)-h_c(y)|=3|d_c(x)-d_c(y)|\le3|x-y|$.</p>
<p>At every grid point, $d_c(g)=0$ and $h_c(g)=0.35$, so all measurements meet the hypothesis. At the midpoint $x=0.2$, the nearest grid distance is $0.2$, giving $h_c(0.2)=0.35-0.6=-0.25$. The coarse measurements therefore cannot guarantee nonnegativity between them.</p>
''')

replace(39, 'Prove the logarithm-versus-square-root limit using first-course calculus, keep the finite regret arithmetic explicit, and separately test the product relative to T.', r'''
<p><strong>Convert a cumulative quantity into an average.</strong> Since $T\ge2$ is positive, divide the stated inequality by $T$ without changing its direction:</p>
<div class="math-block">$$0\le\frac{R_T}{T}
 \le\frac{5\sqrt T\log T}{T}
 =\frac{5\log T}{\sqrt T}.$$</div>
<p>The last expression tends to zero. For example, regarding $T$ as a real variable, the ratio $\log T/\sqrt T$ has the form $\infty/\infty$. L'Hôpital's rule differentiates numerator and denominator:</p>
<div class="math-block">$$\lim_{T\to\infty}\frac{\log T}{\sqrt T}
 =\lim_{T\to\infty}\frac{1/T}{1/(2\sqrt T)}
 =\lim_{T\to\infty}\frac{2}{\sqrt T}=0.$$</div>
<p>The same limit holds at integer iteration counts. The squeeze theorem now gives $R_T/T\to0$, equivalently $R_T=o(T)$: cumulative regret is sublinear. This is a statement about averages, not a claim that every individual trial's regret tends to zero.</p>
<p><strong>Evaluate the actual finite bound.</strong> At $T=10^4$, $\sqrt T=100$ and $\log T=4\log10\approx9.21034$. Therefore</p>
<div class="math-block">$$\frac{R_{10^4}}{10^4}
 \le\frac{5(9.21034)}{100}
 \approx0.46052.$$</div>
<p>This is an upper bound, not the observed average regret. Its fairly large size at this budget is consistent with its eventual limit being zero.</p>
<p><strong>Test the product assertion independently.</strong> Take $a_T=b_T=\sqrt T$. Each satisfies $a_T/T=b_T/T=1/\sqrt T\to0$, so both are $o(T)$. Their product is $a_Tb_T=(\sqrt T)^2=T$. Dividing that product by $T$ gives $1$ at every index, not a quantity tending to zero. Hence $a_Tb_T$ is not $o(T)$. To assess a product, multiply the complete expressions and test the resulting ratio to the specified comparison scale.</p>
''')

replace(40, 'Derive the information interval from the absolute error inequality, test both readings by endpoint containment, and show separate compatible safe and unsafe true temperatures for the rejected reading.', r'''
<p><strong>Translate the sensor statement into information about the true temperature.</strong> The inequality $|x-y|\le0.2$ is equivalent to $-0.2\le x-y\le0.2$. Adding $y$ gives $y-0.2\le x\le y+0.2$. Thus the possible true temperatures are the entire interval $I(y)=[y-0.2,y+0.2]$, in degrees Celsius above reference.</p>
<p>To accept a reading under this rule, every compatible value must satisfy the specification $C=[0,5]$. For intervals this means checking the two extreme values: $I(y)\subseteq C$ exactly when $y-0.2\ge0$ and $y+0.2\le5$.</p>
<p><strong>Reading $y=4.7$.</strong> The information interval is $[4.7-0.2,4.7+0.2]=[4.5,4.9]$. Its lower endpoint is at least $0$ and its upper endpoint at most $5$, so every compatible temperature is acceptable. This reading is certified.</p>
<p><strong>Reading $y=4.9$.</strong> The interval is $[4.7,5.1]$. The lower endpoint is acceptable, but $5.1\gt5$, so the upper endpoint breaks containment. This reading is not certified. It allows both a safe true temperature, such as $x=4.8$, and an unsafe one, such as $x=5.1$; each differs from the reading by at most $0.2$.</p>
<p><strong>Find all accepted readings.</strong> Solving the endpoint conditions gives $y\ge0.2$ and $y\le4.8$, so the complete acceptance interval is $[0.2,4.8]$. At either endpoint, a possible true temperature equals a boundary of $C$ and is permitted, which explains the closed brackets. Rejection means that this information is insufficient to certify the specification; it does not establish physical failure. Certification itself remains conditional on the sensor error bound holding for this reading.</p>
''')

replace(41, 'Show the complete successor interval, solve each containment inequality before intersecting actuator limits, verify all disturbances for the chosen command, and expose the colleague’s changed timing through substitution.', r'''
<p><strong>Fix a command before ranging over the disturbance.</strong> At the known state $x=4.8$, the deterministic term is $1.1x=1.1(4.8)=5.28$. For one fixed $u$, the unknown $w\in[0,0.4]$ therefore gives every successor between $5.28+u$ and $5.68+u$:</p>
<div class="math-block">$$x^+\in[5.28+u,\;5.68+u].$$</div>
<p>Because $w$ enters with positive coefficient $1$, checking these endpoints checks all allowed intermediate disturbances.</p>
<p><strong>Solve containment and enforce the actuator limit.</strong> Keeping this entire interval in $[0,5]$ requires</p>
<div class="math-block">$$\begin{aligned}
5.28+u&\ge0 &&\Longleftrightarrow& u&\ge-5.28,\\
5.68+u&\le5 &&\Longleftrightarrow& u&\le-0.68.
\end{aligned}$$</div>
<p>Those two inequalities give $u\in[-5.28,-0.68]$, but the actuator additionally requires $u\in[-1,0]$. Their intersection is $[-1,-0.68]$, the complete set of robustly allowed commands.</p>
<p><strong>Verify $u=-0.8$.</strong> It lies in this intersection, and substitution gives $x^+=5.28-0.8+w=4.48+w$. Thus $x^+\in[4.48,4.88]\subseteq[0,5]$ for every allowed warming contribution. All contributions to this temperature update have the stated degrees-Celsius units.</p>
<p><strong>Audit the colleague's information.</strong> Their choice gives $x^+=5.28+(-0.28-w)+w=5$. For $0\le w\le0.4$, it ranges from $-0.28$ down to $-0.68$, so its values really are within $[-1,0]$. The problem is the dependency: choosing that value requires knowing the particular $w$ first. It proves $\forall w\ \exists u$, whereas the stated device must supply one $u$ before $w$ arrives, requiring $\exists u\ \forall w$. For example, choosing $-0.28$ as if $w=0$ and then receiving $w=0.4$ would give $x^+=5.4$. The robust command interval avoids this dependence and supplies the required single command.</p>
''')

replace(42, 'Derive the recurrence floor by solving its fixed value, show the shifted induction and worst-case equality sequence, then check neighbouring iteration budgets including strictness and units.', r'''
<p><strong>Remove the constant term before iterating.</strong> The equality recurrence has a steady value $b$ satisfying $b=0.5b+0.03$. Subtracting $0.5b$ gives $0.5b=0.03$, so $b=0.06$ degrees Celsius. Using this identity in the stated inequality gives</p>
<div class="math-block">$$e_{k+1}-0.06
 \le0.5e_k+0.03-0.06
 =0.5(e_k-0.06).$$</div>
<p>Set $z_k=e_k-0.06$. Its initial value is $z_0=0.70-0.06=0.64$. We claim $z_k\le0.64(0.5)^k$. At $k=0$ this is equality. If it holds at $k$, multiply it by the positive number $0.5$ and use the recurrence to obtain $z_{k+1}\le0.5z_k\le0.64(0.5)^{k+1}$. Induction therefore proves</p>
<div class="math-block">$$e_k\le0.06+0.64(0.5)^k
       =0.06+\frac{0.64}{2^k}$$</div>
<p>for every integer $k\ge0$, with the bound measured in degrees Celsius.</p>
<p><strong>Assess the demand $0.04$.</strong> This upper envelope decreases towards $0.06$, which is above $0.04$. It cannot certify the requested tolerance. This does not assert that every actual error is at least $0.06$: actual errors may be smaller than an upper bound. It establishes lack of a universal guarantee because the equality sequence $e_k=0.06+0.64/2^k$ satisfies all the given information and stays above $0.04$.</p>
<p><strong>Find the non-strict budget for $0.07$.</strong> Requiring the envelope to be at most $0.07$ gives</p>
<div class="math-block">$$0.06+\frac{0.64}{2^k}\le0.07
 \ \Longleftrightarrow\
 \frac{0.64}{2^k}\le0.01
 \ \Longleftrightarrow\
 2^k\ge64.$$</div>
<p>Since $2^6=64$, the smallest certified budget is $k=6$, where the bound is exactly $0.07$. At $k=5$ it is $0.06+0.64/32=0.08$, so that smaller budget fails.</p>
<p><strong>Account for a strict demand.</strong> For $e_k\lt0.07$, the envelope must be strictly below $0.07$, requiring $2^k\gt64$. The first integer is now $k=7$, giving $0.06+0.64/128=0.065$. Equality is an allowed recurrence, so $k=6$ cannot guarantee the strict condition even though it guarantees the non-strict one.</p>
''')

replace(43, 'Make necessity universal over every legal command at the boundary, verify feedback legality and both successor bounds for arbitrary state/disturbance, and spell out the all-time induction.', r'''
<p><strong>Find a necessary disturbance limit.</strong> A claim about every $x\in[0,5]$ must in particular work at $x=5$, and a robust command must handle $w=d$. For any legal command $u\ge-1$,</p>
<div class="math-block">$$x^+=1.1(5)+u+d
 \ge5.5-1+d=4.5+d.$$</div>
<p>If $d\gt0.5$, this lower bound already exceeds $5$. Even the strongest permitted cooling cannot help, so no command works at that state and the quantified claim is false. Because $d\ge0$ was stipulated, the only possible range is $0\le d\le0.5$.</p>
<p><strong>Supply a command throughout that range.</strong> Assume $0\le d\le0.5$ and take an arbitrary observed $x\in[0,5]$. Choose the feedback $u(x)=-0.2x$. Multiplying the state bounds by $-0.2$ reverses them and gives $-1\le u(x)\le0$, so the actuator can issue it. The choice depends on $x$, as permitted, and not on the unknown $w$.</p>
<p><strong>Check every disturbance.</strong> With this feedback,</p>
<div class="math-block">$$x^+=1.1x-0.2x+w=0.9x+w.$$</div>
<p>For arbitrary $0\le w\le d$, both terms are nonnegative, so $x^+\ge0$. Also $x^+\le0.9(5)+d=4.5+d\le5$. Therefore every allowed successor lies in $[0,5]$. This proves sufficiency, including the limiting case $d=0.5$, and establishes the exact parameter range $[0,0.5]$.</p>
<p><strong>Extend one step to all time.</strong> Assume $x_0\in[0,5]$, that the stated update holds at every step, and that every disturbance satisfies $w_t\in[0,d]$. Apply $u_t=-0.2x_t$. The initial-state assumption is the induction base. If $x_t$ is in the interval, the calculation above shows the command is legal and $x_{t+1}$ is in the interval for every allowed $w_t$. Induction gives $x_t\in[0,5]$ for all $t\ge0$, even if disturbances vary arbitrarily over time.</p>
<p>Starting outside the interval is not covered by that base case. The earlier feedback for $d=0.4$ was a valid choice for that disturbance range; this feedback additionally handles the exact limiting range $d=0.5$ under the same model and timing assumptions.</p>
''')

replace(44, 'Separate all four requested parts, explicitly negate quantifiers and interval membership, verify the feedback witness and its legal domain, and derive incompatible fixed-input constraints from the endpoints.', r'''
<p><strong>(a) Negate the whole quantified statement.</strong> To make “every state has a successful input” false, there must be one state for which every input fails. Swapping both quantifiers and negating membership gives</p>
<div class="math-block">$$\exists x\in C\ \forall u\in U:\quad f(x,u)\notin C.$$</div>
<p>The domains stay $C=U=[-1,1]$. Since $f(x,u)=2x+u$, the final failure condition means $2x+u\lt-1$ or $2x+u\gt1$; equality at either boundary is not failure.</p>
<p><strong>(b) Prove the original statement with a witness.</strong> Let an arbitrary $x\in[-1,1]$ be given. Choose $u=-x$. The inequalities $-1\le x\le1$ imply $-1\le-x\le1$, so this input belongs to $U$. Substitution gives $f(x,-x)=2x-x=x$, which belongs to $C$. Thus every allowed state has a successful input, and the negation in (a) is false.</p>
<p><strong>(c) Test a command that must work for all states.</strong> Suppose a single $u\in U$ worked for every $x$. At the allowed state $x=1$, keeping $2+u$ in $C$ requires $2+u\le1$, hence $u\le-1$. At the allowed state $x=-1$, keeping $-2+u$ in $C$ requires $-2+u\ge-1$, hence $u\ge1$. No real number can satisfy both conditions. Therefore $\exists u\in U\ \forall x\in C:\ f(x,u)\in C$ is false.</p>
<p><strong>(d) Interpret the information order.</strong> In $\forall x\ \exists u$, the state is known before the input is chosen, so the formula $u=-x$ is a feedback rule. Under it the closed-loop successor equals the current state, so an initial state in $C$ remains there at every step. In $\exists u\ \forall x$, the input has to be fixed before knowing which state will occur. The conflicting endpoint requirements show why this stronger request fails, despite the existence of a valid input at each separate state.</p>
''')

replace(45, 'Organize reachability by rounds using only the preceding set, show all relevant witness radii and the fixed-point check, then quantify the slack lost at the gateway.', r'''
<p><strong>(a) Convert each witness value into its permitted radius.</strong> Here $L=1$, $h=0$ and $\epsilon=0.5$. A witness $x'\in S$ can add $x$ exactly when $|x-x'|\le f(x')-0.5$. The operator also retains every point already in $S$. At each round, use only witnesses in the preceding set; a newly added point can become a witness at the next round.</p>
<p>From $S_0=\{0\}$, the only radius is $f(0)-0.5=1.8-0.5=1.3$. Among the integer grid points, $|x|\le1.3$ selects $0,1$. Thus $S_1=\{0,1\}$.</p>
<p>For the next round, witness $0$ still reaches $0,1$. The new witness $1$ has radius $2.3-0.5=1.8$, selecting $0,1,2$ because their distances from $1$ are $1,0,1$. Point $3$ is at distance $2\gt1.8$ and is not selected. Therefore $S_2=\{0,1,2\}$.</p>
<p>At round three, witness $2$ has radius $1.4-0.5=0.9$, smaller than the distance $1$ to either neighbouring integer, so it certifies only itself. Witnesses $0,1$ reach the sets already listed. Their union adds no point, and $S_3=S_2$. Hence $S_2$ is a fixed point: applying the same operator again gives the same set. Every later iterate is equal to it, so $\bar R_{0.5}(S_0)=\{0,1,2\}$.</p>
<p><strong>(b) Count strict increases.</strong> The grid has $9$ points and the seed has $1$, so there can be at most $|D|-|S_0|=8$ strict increases: each would add at least one previously absent point. Here only $S_0\subsetneq S_1$ and $S_1\subsetneq S_2$ are strict. There are two increases, followed by stabilization.</p>
<p><strong>(c) Explain the loss of the gateway.</strong> Without estimation error, witness $1$ could certify point $3$ with margin $f(1)-|3-1|=2.3-2=0.3$. Subtracting the new error budget $0.5$ turns this margin into $-0.2$, so that link fails. The alternative witness $2$ also fails: $f(2)-0.5-|3-2|=1.4-0.5-1=-0.1$. Witness $0$ is still farther away. Thus no point in the final three-point set can add $3$ or a more distant point.</p>
<p>The zero-error closure in the worked example was $\{0,\ldots,7\}$, containing eight points. With this error allowance it has only three. Error subtracts from a witness's safety margin before that margin can pay for distance; losing a gateway then loses the points that would have relied on it as a later witness. This describes reachability under the stated certificate, not an absolute impossibility for methods using additional information.</p>
''')

replace(46, 'Expand the finite induction algebra, explain the nonnegative double-sum rearrangement with a finite triangular region, calculate both geometric sums, and derive the probability interpretation.', r'''
<p><strong>(a) Prove the finite formula by induction on the number of terms.</strong> Let $S_T=\sum_{t=0}^{T-1}\gamma^t$, with $S_0=0$. At $T=0$, the proposed expression is $(1-\gamma^0)/(1-\gamma)=0$, since $\gamma^0=1$ and $\gamma\ne1$.</p>
<p>For the induction step, assume $S_T=(1-\gamma^T)/(1-\gamma)$. The sum with $T+1$ terms adds the term $\gamma^T$, so</p>
<div class="math-block">$$\begin{aligned}
S_{T+1}
 &=S_T+\gamma^T\\
 &=\frac{1-\gamma^T}{1-\gamma}+\gamma^T\\
 &=\frac{1-\gamma^T+\gamma^T(1-\gamma)}{1-\gamma}\\
 &=\frac{1-\gamma^{T+1}}{1-\gamma}.
\end{aligned}$$</div>
<p>The third line uses a common denominator, and the fourth cancels $-\gamma^T+\gamma^T$. This is the desired formula at $T+1$. Induction proves it for every integer $T\ge0$.</p>
<p><strong>(b) Count each discounted term by its time index.</strong> For $t\ge1$, the identity $t=\sum_{s=1}^{t}1$ expresses $t$ as $t$ copies of $1$. The term at $t=0$ is zero. Consequently</p>
<div class="math-block">$$\begin{aligned}
\sum_{t=0}^{\infty}t\gamma^t
 &=\sum_{t=0}^{\infty}\sum_{s=1}^{t}\gamma^t\\
 &=\sum_{s=1}^{\infty}\sum_{t=s}^{\infty}\gamma^t\\
 &=\sum_{s=1}^{\infty}\frac{\gamma^s}{1-\gamma}\\
 &=\frac1{1-\gamma}\,\frac{\gamma}{1-\gamma}
 =\frac{\gamma}{(1-\gamma)^2}.
\end{aligned}$$</div>
<p>In the second line, the same pairs of indices are counted: $1\le s\le t$. For a finite horizon, these pairs form a finite triangular region, and either order adds exactly the same terms. As the region grows, every term is nonnegative because $0\le\gamma\lt1$. Thus enlarging it can only increase the partial sum, and the two orders have the same supremum; no cancellation or conditional convergence obstructs the exchange. The third line uses the geometric tail formula; the fourth uses $\sum_{s=1}^{\infty}\gamma^s=\gamma/(1-\gamma)$. At $\gamma=0$ the sum and the resulting formula are both zero.</p>
<p><strong>(c) Substitute and interpret.</strong> For $\gamma=0.9$, the weighted sum is $0.9/(0.1)^2=0.9/0.01=90$. Multiplying by $1-\gamma=0.1$ gives $9$.</p>
<p>Define probabilities $p_t=(1-\gamma)\gamma^t$ for $t=0,1,\ldots$. They are nonnegative and sum to $(1-\gamma)/(1-\gamma)=1$, so they describe a random time $\tau$ with $\mathbb P(\tau=t)=p_t$. Its mean is $\mathbb E[\tau]=\sum_ttp_t=(1-\gamma)\sum_tt\gamma^t=\gamma/(1-\gamma)=9$. In this precise sense discounting weights time as a random horizon with mean time index $9$ steps.</p>
''')

replace(47, 'Explain attainment in each bound, carefully distinguish the signed sequence from the local graded example, derive the trigonometric supremum, and show both optimizing responses in the continuous minimax problem.', r'''
<p><strong>(a) Identify the actual output set.</strong> For $x\ge0$,</p>
<div class="math-block">$$\frac{x}{1+x}=1-\frac1{1+x}.$$</div>
<p>The denominator is positive, so these values are nonnegative and strictly below $1$. The value $0$ is attained at $x=0$. As $x\to\infty$, the fraction $1/(1+x)$ tends to zero, and the outputs approach $1$. Hence $\inf A=\min A=0$ and $\sup A=1$. There is no maximum, because no finite $x$ gives $1$; increasing $x$ gives a larger output.</p>
<p><strong>(b) Separate the two parity subsequences.</strong> Here the factor $(-1)^t$ multiplies the whole bracket. Thus $a_{2k}=1+1/(2k+1)$ decreases from $2$ to $1$, while $a_{2k+1}=-1-1/(2k+2)$ increases from $-3/2$ to $-1$. The first values are $2,-3/2,4/3,-5/4,\ldots$.</p>
<p>Every term is between $-3/2$ and $2$, and both bounds are attained: $\sup=\max=2$ at $t=0$, and $\inf=\min=-3/2$ at $t=1$. Every late tail still has both parities; its upper limiting value is $1$ and its lower limiting value is $-1$. Therefore $\limsup a_t=1$ and $\liminf a_t=-1$. The sequence does not converge, despite having a largest and a smallest term.</p>
<p><strong>(c) Optimize the sum at one common input.</strong> The angle-addition identity gives</p>
<div class="math-block">$$\sin(x+\pi/4)
 =\frac{\sin x+\cos x}{\sqrt2},
 \qquad
 \sin x+\cos x=\sqrt2\sin(x+\pi/4).$$</div>
<p>Since $\sin$ never exceeds $1$, the sum never exceeds $\sqrt2$, and at $x=\pi/4$ it equals $\sqrt2$. Thus $\sup_x(\sin x+\cos x)=\sqrt2\approx1.414$. Separately, $\sup_x\sin x=1$ and $\sup_x\cos x=1$, so their sum is $2$. Those separate optima occur at different inputs: $\sin$ is $1$ at $\pi/2$ and $\cos$ is $1$ at $0$, and they cannot both equal $1$ at a common input. This explains the strict inequality $\sqrt2\lt2$.</p>
<p><strong>(d) Choose the inner optimizing response first.</strong> Fix $x\in[-1,1]$. If $x\ge0$, the largest $xy$ occurs at $y=1$ and is $x$. If $x\lt0$, it occurs at $y=-1$ and is $-x$. In both cases $\sup_{y\in[-1,1]}xy=|x|$. Minimizing this over $x$ gives $0$, attained at $x=0$.</p>
<p>In the other order, fix $y$. If $y\ge0$, the smallest $xy$ occurs at $x=-1$; if $y\lt0$, it occurs at $x=1$. Thus $\inf_{x\in[-1,1]}xy=-|y|$. Its largest value over $y$ is $0$, at $y=0$. We conclude</p>
<div class="math-block">$$\inf_x\sup_y\phi(x,y)=0
       =\sup_y\inf_x\phi(x,y).$$</div>
<p>There is no minimax gap in this example. At $(0,0)$, both $\phi(0,y)$ and $\phi(x,0)$ are zero for every allowed opponent's choice, so neither player can improve its outcome by changing only its own coordinate; $(0,0)$ is a saddle point.</p>
''')

replace(48, 'Resolve each existence question by a lower bound and attaining witness or an explicit approaching sequence; derive the constrained quadratic identity and every parameter case of the sublevel set.', r'''
<p><strong>(a) $e^{-x}$ on $x\ge0$.</strong> Every finite $x$ gives $e^{-x}\gt0$, so $0$ is a lower bound. Taking $x=n$ and sending $n\to\infty$ gives $e^{-n}\to0$, showing that no larger number is a lower bound. Thus the infimum is $0$, but it is never attained, and a minimum does not exist. The domain is unbounded, so the compact-domain extreme value theorem does not apply.</p>
<p><strong>(b) $x^2-x$ on $[0,1]$.</strong> This polynomial is continuous and the interval is nonempty and compact, so a minimum exists. To locate it and verify that it is global, complete the square:</p>
<div class="math-block">$$x^2-x=(x-\tfrac12)^2-\tfrac14\ge-\tfrac14.$$</div>
<p>Equality occurs only at $x=1/2$, which is in the domain. The unique minimum is $-1/4$. The calculus calculation $f'(x)=2x-1=0$ gives the same point; the square verifies that neither an endpoint nor any other input has a smaller value.</p>
<p><strong>(c) The constrained squared norm.</strong> Write $s=u_1+u_2$ and note that feasibility means $s\ge1$. Expanding squares gives</p>
<div class="math-block">$$\begin{aligned}
\|u\|^2=u_1^2+u_2^2
 &=\frac{(u_1+u_2)^2+(u_1-u_2)^2}{2}\\
 &\ge\frac{s^2}{2}\ge\frac12.
\end{aligned}$$</div>
<p>The first inequality drops a nonnegative square; the second uses $s\ge1$. At $u^\ast=(1/2,1/2)$, the constraint holds with equality and the objective is $1/4+1/4=1/2$. Hence a minimum exists and equals $1/2$. Equality requires $u_1-u_2=0$ and $s=1$, so this minimizer is unique. Although the feasible half-space is unbounded, it is closed and nonempty and the objective is coercive; the explicit lower-bound-and-witness calculation here establishes the result directly.</p>
<p><strong>(d) The unconstrained linear maximum.</strong> Choose $u=(s,s)$. Its objective is $u_1+u_2=2s$, which grows without bound as $s\to\infty$. Any proposed maximum can be exceeded by a larger $s$. Thus there is no maximum; the supremum is $+\infty$.</p>
<p><strong>(e) Split the parameter cases before rearranging.</strong> Since $1+x^2\gt0$, we always have $0\le x^2/(1+x^2)\lt1$.</p>
<ul>
<li>If $c\lt0$, no value meets the inequality, so the sublevel set is empty. The empty set is compact.</li>
<li>If $0\le c\lt1$, multiplying by the positive denominator and rearranging gives $x^2\le c(1+x^2)$, hence $(1-c)x^2\le c$. Because $1-c\gt0$, division preserves the inequality and gives $x^2\le c/(1-c)$. The set is the closed bounded interval $[-\sqrt{c/(1-c)},\sqrt{c/(1-c)}]$, so it is compact. At $c=0$, this interval is the singleton $\{0\}$.</li>
<li>If $c\ge1$, every real $x$ satisfies the inequality, so the set is all of $\mathbb R$ and is not compact because it is unbounded.</li>
</ul>
<p>Therefore the sublevel set is compact exactly when $c\lt1$, including negative $c$. Its emptiness in the negative case does not imply that a minimizer exists there: the extreme value theorem also requires a nonempty domain.</p>
''')

replace(49, 'Show all growth-ratio comparisons, derive the regret limit and monotonicity, bracket the exact eventual integer cutoff numerically, and explain cubic timing and grid-count assumptions.', r'''
<p><strong>(a) Order growth as $T\to\infty$.</strong> The order is $(\ln T)^3\ll\sqrt T\ll T^{2/3}\ll T/\ln T$, where $f\ll g$ means $f/g\to0$. It is an eventual growth comparison, not an ordering at every small value of $T$.</p>
<p>For the first comparison, put $s=\ln T$, so $(\ln T)^3/\sqrt T=s^3/e^{s/2}$. Three applications of L'Hôpital's rule, differentiating the numerator and denominator each time, give the limiting ratio $48/e^{s/2}\to0$. For the middle comparison, $\sqrt T/T^{2/3}=T^{-1/6}\to0$. For the last,</p>
<div class="math-block">$$\frac{T^{2/3}}{T/\ln T}
 =\frac{\ln T}{T^{1/3}}
 \longrightarrow0,$$</div>
<p>because L'Hôpital's rule gives $(1/T)/((1/3)T^{-2/3})=3/T^{1/3}\to0$. These ratios justify the stated order.</p>
<p><strong>(b) Divide by the number of trials.</strong> The bound implies $0\le R_T/T\le b(T):=4\ln T/\sqrt T$. The ratio $\ln T/\sqrt T$ tends to zero: differentiating numerator and denominator gives $(1/T)/(1/(2\sqrt T))=2/\sqrt T\to0$. Thus the squeeze theorem proves $R_T/T\to0$, or sublinear regret.</p>
<p>For a permanent tolerance bound, first check where $b$ decreases. Differentiating gives</p>
<div class="math-block">$$b'(T)=4T^{-3/2}(1-\tfrac12\ln T).$$</div>
<p>This is nonpositive for $T\ge e^2$. We can therefore locate its late crossing of $0.1$ numerically, then use monotonicity for all larger budgets. Useful values are $b(10^4)\approx0.36841$ and $b(10^5)\approx0.14563$. Narrowing the interval around the crossing gives</p>
<table><thead><tr><th>$T$</th><th>$4\ln T/\sqrt T$</th><th>Meets $0.1$?</th></tr></thead><tbody>
<tr><td>$246{,}638$</td><td>$0.1000000922$ (approximately)</td><td>No</td></tr>
<tr><td>$246{,}639$</td><td>$0.0999999221$ (approximately)</td><td>Yes</td></tr>
</tbody></table>
<p>Thus $T=246{,}639$ is the first integer cutoff from which this bound stays at most $0.1$. Any smaller cutoff would still include the failing index $246{,}638$. An earlier isolated small value need not determine an eventual cutoff. These numbers concern the upper bound; actual regret may be smaller.</p>
<p><strong>(c) Translate a size increase into cubic work.</strong> The matrix dimension increases by $4000/1000=4$. Assuming the same implementation and approximately constant time per arithmetic operation, cubic scaling multiplies the work by $4^3=64$. The estimate is $0.05(64)=3.2$ seconds. Big-$O$ gives the scaling model, not an exact wall-clock guarantee.</p>
<p><strong>(d) Count combinations across axes.</strong> Each grid point independently chooses one of $20$ positions on each of six axes, so the total is $20^6=(20^3)^2=8000^2=64{,}000{,}000=6.4\cdot10^7$. It is a product of choices, not $20$ times the number of axes. With ten axes, the same rule gives $20^{10}=1.024\cdot10^{13}$ points, showing the steep cost of increasing dimension.</p>
''')

replace(50, 'Verify every Banach hypothesis, carry the logarithmic sign reversal through the iteration cutoff, distinguish the local-rate explanation from a certified 32-step result, and derive the a posteriori bound from future-step tails.', r'''
<p><strong>(a) Check that the interval is preserved.</strong> Write $c=\cos1$ and $J=[c,1]$, with $c\approx0.5403$. The interval lies in $[0,\pi/2]$, where $\cos$ is decreasing. Hence its image is $g(J)=[\cos1,\cos(\cos1)]=[c,\cos c]$. The upper endpoint satisfies $\cos c\le1$, and $\cos c\ge\cos1=c$ because $c\le1$. Therefore $g(J)\subseteq J$; the image endpoints are approximately $0.5403$ and $0.8576$.</p>
<p><strong>Check contraction, not just preservation.</strong> For distinct $x,y\in J$, the mean value theorem supplies $\xi$ between them such that $\cos x-\cos y=-\sin\xi\,(x-y)$. Since $0\le\xi\le1$ and $\sin$ increases on this interval, $|\sin\xi|\le\sin1$. Thus</p>
<div class="math-block">$$|\cos x-\cos y|\le L|x-y|,
 \qquad L=\sin1\approx0.8415\lt1.$$</div>
<p>The inequality also holds when $x=y$. The interval is nonempty and closed, and we verified the self-map and strict-contraction properties. Banach's theorem therefore gives one fixed point in $J$, $x^\ast\approx0.739085$, and convergence from every start in $J$.</p>
<p><strong>(b) Use the bound that needs only the first step.</strong> At $x_0=1$, the next value is $x_1=\cos1$, so $|x_1-x_0|=1-\cos1\approx0.4597$. The a priori bound is</p>
<div class="math-block">$$|x_k-x^\ast|
 \le\frac{L^k}{1-L}(1-\cos1).$$</div>
<p>To guarantee the target, require $L^k\le(1-L)10^{-6}/(1-\cos1)$. Both sides are positive, so logarithms preserve their order. Dividing by $\ln L\lt0$ then reverses the inequality:</p>
<div class="math-block">$$k\ge
 \frac{\ln\big((1-\cos1)/((1-\sin1)10^{-6})\big)}
      {\ln(1/\sin1)}
 \approx86.2098.$$</div>
<p>The first integer meeting this certificate is $87$. As a rough arithmetic check, $1-L\approx0.1585$, the numerator is approximately $14.88$ and the denominator approximately $0.1726$. The integer decision uses the original sine and cosine values, rather than treating their rounded displays as exact.</p>
<p><strong>(c) Explain why the actual run is faster.</strong> The constant $L$ bounds the slope everywhere in $J$. Once the iterates are near $x^\ast$, the slope magnitude is about $\sin x^\ast\approx0.674$, substantially smaller. A geometric estimate using this local factor and the starting error $1-x^\ast\approx0.261$ gives $\ln(0.261\cdot10^6)/\ln(1/0.674)\approx31.6$, suggesting $32$ iterations. This explains the gap but is not itself a uniform guarantee.</p>
<p>A certified interval calculation can check the actual conclusion. The fixed point lies between $0.7390851331$ and $0.7390851333$, and the thirty-second iterate lies between $0.73908599959$ and $0.73908599970$. These intervals place the iterate above the fixed point and bound its error by $0.73908599970-0.7390851331=0.0000008666\lt10^{-6}$. Such enclosures track rounding error; simply comparing rounded iterates with a rounded fixed point is not a certificate. The global a priori bound must also cover starts elsewhere in $J$.</p>
<p><strong>(d) Use the observed last step to bound all remaining movement.</strong> Let $d_k=|x_k-x_{k-1}|$. Contraction gives $|x_{k+1}-x_k|\le Ld_k$, the next step is at most $L^2d_k$, and so on. The total remaining distance to the limit is at most the sum of these step lengths:</p>
<div class="math-block">$$|x^\ast-x_k|
 \le(L+L^2+L^3+\cdots)d_k
 =\frac{L}{1-L}d_k.$$</div>
<p>At $k=10$, the supplied rounded values give $d_{10}\approx|0.744237-0.731404|=0.012833$. Also $L/(1-L)\approx5.31$, so the a posteriori bound is approximately $5.31(0.012833)\approx0.068$. The true error is about $0.0052$, and the a priori bound at this index is about $0.52$. The recent-step bound improves the certificate, but still uses the worst slope and a triangle-inequality sum, so it remains larger than the actual error.</p>
''')

retained_rationales = {
1: 'The existing answer evaluates all six candidate squares, identifies the positive subset, checks membership at equality, and refutes inclusion with the concrete element 3. The membership/inclusion distinction is explicitly explained.',
2: 'The answer explains the selection rule for each of the four operations, shows which elements are removed for the difference, and states the universe-dependent complement. Each requested set and its method is present.',
3: 'All four truth judgments have their appropriate logical support: nonnegative squares, impossibility of a negative square, the dependent witness y=x+2, and the contradiction from x=y for a shared witness.',
4: 'Both negations keep their domains and change each quantifier and inequality correctly. The witnesses x=0 and y=x are checked and used to establish falsity of the originals, including strictness and equality.',
5: 'The solution separately states and assesses the implication, converse and contrapositive, uses -4 to refute the converse, derives the interval from the squared bound, and explains necessary versus sufficient conditions.',
6: 'Both set equalities are justified by containment and membership. The intersection proof includes 0 and excludes every nonzero x by choosing k>1/|x| and checking the failed interval.',
7: 'The answer computes both endpoint-sensitive complement intervals and follows an arbitrary x through each membership equivalence, explaining why this proves equality of the sets.',
8: 'The allowed input list is given for each state, every successful dependent choice is supplied, both possible fixed inputs are ruled out, and the fully quantified negation is assessed with the distinction explained.',
9: 'Necessity is checked at x=1 and sufficiency supplies u=-x with its actuator bound; the fixed-input request is disproved using the incompatible endpoint requirements. Both quantified claims and the full parameter range are justified.',
10: 'The answer evaluates every domain element and removes duplicate outputs to form the image. It demonstrates noninjectivity using distinct inputs and nonsurjectivity using the missing declared output 9.',
11: 'The two numerical compositions apply the right-hand function first and show both intermediate outputs. The general expressions and expansion of (2x-1)^2 are given, establishing the noncommuting order.',
12: 'The fixed-point equation is rearranged to the value 1; all three iterates are explicitly substituted. Four error magnitudes are listed and the identity g(x)-1=(x-1)/4 explains the repeated factor.',
16: 'The numerical noninjective example is computed, then each inclusion in the general set equality is proved with an arbitrary output and its input witnesses. The exact use of injectivity to identify those witnesses is visible.',
17: 'Every requested iterate displays its previous set and image, the unchanged third iterate proves stabilization, and the inclusion proof establishes monotonicity. The separate 3-4 cycle explains the absent states.',
18: 'Each example checks a distinct Banach hypothesis, solves the fixed-point condition independently, and identifies where the point belongs or fails to belong. The alternating run is stated and theorem failure is distinguished from falsity of all conclusions.',
19: 'Completing the square gives the full general inequality, and the answer names nonnegativity of a square and the equality condition x=-1. It explicitly explains why the arbitrary-input argument proves a universal statement.',
20: 'The contrapositive is identified, an odd integer is represented by 2m+1, every expansion and factorization step is displayed, and integrality of the new coefficient establishes oddness of its square.',
21: 'Each of the three counterexamples checks the proposed premise and the failed conclusion numerically. The answer explains why one counterexample refutes a universal statement.',
22: 'The induction answer labels the empty-sum base case, the exact hypothesis, the split final term, the algebra using the hypothesis, and the induction conclusion. Each substantive step is justified.',
24: 'The one-step interval bounds are derived and contained in C; the induction identifies the initial-state hypothesis as its base and uses only current membership in its step. The example x0=2 shows what fails without that hypothesis.',
25: 'The proof introduces a nonnegative distance between two hypothetical fixed points, applies the contraction, and forces the distance to zero. The counterexample has a self-map and the required factor but no in-domain fixed point, making uniqueness distinct from existence.',
26: 'The circular assumption is identified. The quantitative induction hypothesis establishes membership in the local validity set before the bound on F is used, and each inequality proves the next bound and membership.',
27: 'The concrete five states and repeating two-state cycle are given. The arbitrary-map argument invokes pigeonhole, derives identical futures by the fixed deterministic rule, and proves the four-state horizon. The time-dependent counterexample checks the stated limitation.',
28: 'The four terms, limit, positivity of the denominator, strict inequality rearrangement, integer cutoff and preceding failing term are all worked explicitly. The all-later-times quantifier is checked using monotonicity.',
33: 'Both optimization orders evaluate each required row maximum or column minimum using the actual four entries. The minimizing and maximizing choices are stated, and the response advantage explains the strict gap.',
35: 'Each of the three domains is handled separately by an approaching sequence or an attained lower bound. The theorem conditions are checked for the compact interval, and a direct argument explains attainment on noncompact R without reversing a sufficient condition.',
37: 'The solution gives explicit lower and upper constants with their common threshold, shows the bounds on each lower-order term, and evaluates the ratio to distinguish Theta from little-o.',
38: 'Both error inequalities are solved for the iteration budget and multiplied by their stated per-iteration operation costs. The factor-of-two comparison and its worst-case/sufficient interpretation answer every requested part.'
}
assert len(replacements) == 22 and len(retained_rationales) == 28
assert set(replacements) | set(retained_rationales) == set(range(1, 51))
assert not set(replacements) & set(retained_rationales)

rows = []
for original in page['exercises']:
    ordinal = original['ordinal']
    replacement = replacements.get(ordinal, original['solution']['html'])
    assert sha256(original['solution']['html'].encode()).hexdigest() == original['solution']['sha256']
    author_path = ROOT / original['authoring_file']
    a = original['authoring']['solution_range']
    assert author_path.read_bytes()[a['start_byte']:a['end_byte']].decode() == original['solution']['html']
    rows.append({
        'inventory_key': original['inventory_key'],
        'source_file': original['source_file'],
        'authoring_file': original['authoring_file'],
        'ordinal': ordinal,
        'anchor': original['anchor'],
        'label': original['label'],
        'original_solution_sha256': original['solution']['sha256'],
        'original_source_sha256': original['source_sha256'],
        'original_authoring_source_sha256': original['authoring']['source_sha256'],
        'original_question_sha256': original['problem']['sha256'],
        'original_hint_sha256': [h['disclosure']['sha256'] for h in original['hints']],
        'decision': 'replace' if ordinal in replacements else 'retain',
        'replacement_html': replacement,
        'replacement_sha256': sha256(replacement.encode()).hexdigest(),
        'thoroughness_rationale': rationales.get(ordinal, retained_rationales.get(ordinal)),
        'review_family': 'application' if original['authoring_file'].startswith('book/chapters/') else (
            'mixed' if ordinal >=44 else 'proof' if 19<=ordinal<=27 else 'conceptual_and_calculation'),
        'audience': 'First-course linear algebra and single-variable calculus; explain the additional local mathematical concepts.',
        'question_hint_notation_and_primary_conclusions_preserved': True,
        'pedagogical_status': 'author_review_complete_pending_independent_review',
    })
    assert rows[-1]['thoroughness_rationale']
    assert (replacement == original['solution']['html']) == (rows[-1]['decision'] == 'retain')

document = {
    'schema': 'solution-depth.draft.v1',
    'status': 'draft_all_fifty_author_reviewed_pending_independent_review',
    'author': '/root/review_diagonal35',
    'created_at_utc': datetime.now(timezone.utc).isoformat(),
    'page': 'SafeLearning/primer-basics.html',
    'baseline': ref(BASELINE),
    'baseline_manifest': ref('book/solutions/baseline-source90/manifest.json'),
    'page_contract': ref('page_contract.md'),
    'review_criteria': ref('book/solutions/README.md'),
    'source_refs': [ref('SafeLearning/primer-basics.html'), ref('book/chapters/primer-basics.html')],
    'counts': {'reviewed_exercises': 50, **dict(Counter(r['decision'] for r in rows)), 'book_lab_exercises': 4},
    'exercises': rows,
    'numerical_checks': {
        'regret_at_246638': '4*ln(246638)/sqrt(246638) = approximately 0.10000009218841957',
        'regret_at_246639': '4*ln(246639)/sqrt(246639) = approximately 0.09999992211898176',
        'cosine_apriori_real_cutoff': 'approximately 86.20984381083345; integer cutoff 87',
        'cosine_posteriori_using_question_roundings': 'approximately 0.06811748079652243',
        'cosine_apriori_at_ten': 'approximately 0.5161251451053713',
        'cosine_32_certified_enclosures': {
            'source': ref('verification/lean/SafeLearning/CompleteFoundationsCosineIterates.lean'),
            'declarations': ['SafeLearning.CompleteFoundationsCosineIterates.actual_fixed_point_certified_enclosure',
                             'SafeLearning.CompleteFoundationsCosineIterates.actual_source_first_thirty_two_iterations_enclosed',
                             'SafeLearning.CompleteFoundationsCosineIterates.actual_thirty_two_iterations_meet_the_source_tolerance'],
            'fixed_point': '(0.7390851331,0.7390851333)',
            'iterate32': '[0.73908599959,0.73908599970]',
            'derived_error_upper_bound': '0.0000008666 < 0.000001',
        },
    },
    'new_external_citations': [],
    'canonical_source_owner_selection_progress_publication_mutations': False,
    'whole_page_reserialized': False,
    'independent_pedagogical_approval_claimed': False,
    'rendered_qa_claimed': False,
    'scope': 'Fifty individually read exercise/solution pairs; only solution-body replacements proposed. Lab integration must edit its authored fragment. Mathematical checkpoints and coverage records remain unchanged.',
}
(ROOT / OUT).write_text(json.dumps(document, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'draft': ref(OUT), 'counts': document['counts'],
                  'independent_review_pending': True, 'canonical_edits': False}))
