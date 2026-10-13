#!/usr/bin/env python3
"""Author only exact solution-body drafts for the probability primer."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
BASELINE = ROOT / "book/solutions/baseline-source90/pages/primer-probability.html.json"
AUTHORED = {}


def add(locator, html, improvements):
    AUTHORED["primer-probability.html" + locator] = {
        "replacement_html": html.strip() + "\n",
        "specific_improvements": improvements,
    }


add("#pr-ready-3", r"""
<p>Multiply a column by a row: the entry in position $(i,j)$ is $v_iv_j$. Here this gives</p>
<div class="math-block">$$vv^\top=
\begin{bmatrix}1\\2\end{bmatrix}\begin{bmatrix}1&2\end{bmatrix}
=\begin{bmatrix}1\cdot1&1\cdot2\\2\cdot1&2\cdot2\end{bmatrix}
=\begin{bmatrix}1&2\\2&4\end{bmatrix}.$$</div>
<p>The matrix is symmetric. To check positive semidefiniteness, take an arbitrary $w=(w_1,w_2)^\top$, multiply, and collect the terms:</p>
<div class="math-block">$$w^\top vv^\top w=w_1^2+4w_1w_2+4w_2^2=(w_1+2w_2)^2\ge0.$$</div>
<p>This works for every $w$, which is exactly the required quadratic-form condition. It does not make the matrix positive definite: $w=(-2,1)^\top$ is nonzero but gives $(-2+2)^2=0$. More generally, $w^\top vv^\top w=(v^\top w)^2$; averages of these nonnegative quantities explain why covariance matrices are positive semidefinite.</p>
""", ["Show all four outer-product entries.", "Expand and factor the arbitrary quadratic form; check the nonzero zero-direction."])

add("#pr-extra-1", r"""
<p>A discrete probability law must assign nonnegative weights whose total is one. All three weights are nonnegative, and</p>
<div class="math-block">$$\frac12+\frac14+\frac14=\frac24+\frac14+\frac14=1.$$</div>
<p>The event $X\ge2$ includes the two distinct outcomes $2$ and $4$. Their events are disjoint, so their probabilities add:</p>
<div class="math-block">$$\mathbb P(X\ge2)=\mathbb P(X=2)+\mathbb P(X=4)=\frac14+\frac14=\frac12.$$</div>
<p>For the mean, multiply each value by its probability, including the zero outcome:</p>
<div class="math-block">$$\mathbb E[X]=0\left(\frac12\right)+2\left(\frac14\right)+4\left(\frac14\right)
=0+\frac12+1=\frac32.$$</div>
<p>The mean is $1.5$, even though the cost can only be $0$, $2$ or $4$. An expectation describes a weighted average, not an additional possible outcome.</p>
""", ["Separate normalization, event addition and expectation.", "Show the fraction arithmetic instead of only its final value."])

add("#pr-extra-2", r"""
<p>Use the law from the preceding exercise, whose mean is $m=\mathbb E[X]=3/2$. For the second moment, square each possible value before weighting:</p>
<div class="math-block">$$\mathbb E[X^2]=0^2\left(\frac12\right)+2^2\left(\frac14\right)+4^2\left(\frac14\right)
=0+\frac44+\frac{16}4=5.$$</div>
<p>The variance is the average squared distance from the mean. Expanding that square gives $\operatorname{Var}(X)=\mathbb E[X^2]-m^2$, so</p>
<div class="math-block">$$\operatorname{Var}(X)=5-\left(\frac32\right)^2=\frac{20}4-\frac94=\frac{11}4=2.75,
\qquad \operatorname{SD}(X)=\sqrt{\frac{11}4}=\frac{\sqrt{11}}2\approx1.658.$$</div>
<p>For $Y=3X+1$, linearity of expectation gives $\mathbb E[Y]=3(3/2)+1=9/2+2/2=11/2$. The constant shift disappears when we subtract this new mean:</p>
<div class="math-block">$$Y-\mathbb E[Y]=3X+1-\left(3\mathbb E[X]+1\right)=3(X-\mathbb E[X]).$$</div>
<p>Squaring multiplies the distances by $9$, and then averaging gives $\operatorname{Var}(Y)=9\operatorname{Var}(X)=99/4=24.75$. A shift changes the mean; scaling changes the variance by the square of the scale.</p>
""", ["Explain the second-moment identity and show its arithmetic.", "Derive the transformed centered variable before scaling the variance."])

add("#pr-extra-3", r"""
<p>Each of $X=-1,0,1$ has probability $1/3$, and $Y=X^2$ is respectively $1,0,1$. Compute the means and the cross moment from those three possibilities:</p>
<div class="math-block">$$\mathbb E[X]=\frac{-1+0+1}{3}=0,\qquad
\mathbb E[Y]=\frac{1+0+1}{3}=\frac23,\qquad
\mathbb E[XY]=\mathbb E[X^3]=\frac{-1+0+1}{3}=0.$$</div>
<p>Thus $\operatorname{Cov}(X,Y)=\mathbb E[XY]-\mathbb E[X]\mathbb E[Y]=0$. The diagonal entries need the two variances. Since $\mathbb E[X^2]=2/3$ and $Y^2=Y$ for the values $0,1$,</p>
<div class="math-block">$$\operatorname{Var}(X)=\frac23-0^2=\frac23,\qquad
\operatorname{Var}(Y)=\frac23-\left(\frac23\right)^2=\frac69-\frac49=\frac29.$$</div>
<p>The covariance matrix is consequently $\begin{bmatrix}2/3&0\\0&2/9\end{bmatrix}$. Nevertheless, the variables are dependent. In particular, $Y=0$ occurs exactly when $X=0$, so $\mathbb P(X=0\mid Y=0)=1$, whereas $\mathbb P(X=0)=1/3$. Independence would require these probabilities to agree. Covariance zero detects the absence of this linear association; it does not rule out the nonlinear relation $Y=X^2$.</p>
""", ["Compute both second moments and the cross moment explicitly.", "Use a conditional-probability contradiction to establish dependence."])

add("#pr-extra-4", r"""
<p>For a fair die, each of the six outcomes has probability $1/6$. The events are $A=\{2,4,6\}$ and $B=\{4,5,6\}$, so $\mathbb P(A)=3/6=1/2$ and $\mathbb P(B)=3/6=1/2$.</p>
<p>To have both an even result and a result greater than $3$, the outcome must be $4$ or $6$. Therefore $A\cap B=\{4,6\}$ and $\mathbb P(A\cap B)=2/6$. Since $\mathbb P(B)>0$, conditioning is well defined:</p>
<div class="math-block">$$\mathbb P(A\mid B)=\frac{\mathbb P(A\cap B)}{\mathbb P(B)}
=\frac{2/6}{3/6}=\frac26\frac63=\frac23.$$</div>
<p>Equivalently, after learning $B$, only the equally likely outcomes $4,5,6$ remain; two of those three are even. Conditioning changes the reference group, which is why the answer differs from the unconditional probability $1/2$.</p>
""", ["State the positive-denominator condition.", "Show the intersection and the division of fractions."])

add("#pr-extra-5", r"""
<p>Write $F$ for a fault and $A$ for an alarm. The supplied rates are $\mathbb P(F)=0.1$, $\mathbb P(A\mid F)=0.8$ and $\mathbb P(A\mid F^c)=0.2$. Count hypothetical runs to keep the different denominators visible:</p>
<table><thead><tr><th>Among 1000 runs</th><th>Alarm</th><th>No alarm</th><th>Total</th></tr></thead><tbody><tr><td>Fault</td><td>80</td><td>20</td><td>100</td></tr><tr><td>No fault</td><td>180</td><td>720</td><td>900</td></tr><tr><td>Total</td><td>260</td><td>740</td><td>1000</td></tr></tbody></table>
<p>The faulty alarm count is $0.8(100)=80$; the healthy alarm count is $0.2(900)=180$. These are disjoint routes into an alarm, so total probability gives</p>
<div class="math-block">$$\mathbb P(A)=0.8(0.1)+0.2(0.9)=0.08+0.18=0.26.$$</div>
<p>After an alarm, the reference group is the $260$ alarming runs. Only $80$ of them are faulty:</p>
<div class="math-block">$$\mathbb P(F\mid A)=\frac{\mathbb P(F\cap A)}{\mathbb P(A)}
=\frac{0.08}{0.26}=\frac{80}{260}=\frac4{13}\approx0.3077.$$</div>
<p>The sensitivity $0.8$ is the alarm fraction among faulty runs, not the fault fraction among alarming runs. The large healthy population accounts for the difference. These counts illustrate the assumed law; they are not a new observed data set.</p>
""", ["Make both routes into alarms visible in a four-cell table.", "Explain the denominator change from sensitivity to posterior fault probability."])

add("#pr-extra-6", r"""
<p>The model label has probabilities $\mathbb P(L=1)=\mathbb P(L=2)=1/2$. Averaging the conditional means gives the unconditional mean:</p>
<div class="math-block">$$m=\mathbb E[X]=\frac12\mathbb E[X\mid L=1]+\frac12\mathbb E[X\mid L=2]
=\frac12(0)+\frac12(4)=2.$$</div>
<p>Total variance separates spread within each model from disagreement between the model means. The first term is $\mathbb E[\operatorname{Var}(X\mid L)]=(1+1)/2=1$. The conditional mean $m_L$ takes values $0$ and $4$, so</p>
<div class="math-block">$$\operatorname{Var}(m_L)=\frac12(0-2)^2+\frac12(4-2)^2
=\frac12(4)+\frac12(4)=4.$$</div>
<p>To see why these terms add, write $X-m=(X-m_L)+(m_L-m)$ and expand the square. The cross term has expectation zero: conditional on $L$, the first factor $X-m_L$ has mean zero and the second is fixed. Thus $\operatorname{Var}(X)=1+4=5$.</p>
<p>A second-moment check gives the same result. The conditional second moments are $1+0^2=1$ and $1+4^2=17$, so $\mathbb E[X^2]=(1+17)/2=9$ and $9-m^2=9-4=5$. Neither argument needs Gaussian conditional laws; the supplied finite means and variances suffice.</p>
""", ["Justify why the total-variance cross term vanishes.", "Add an independent second-moment check without imposing Gaussianity."])

add("#pr-extra-7", r"""
<p>Use row distributions because each row of $P$ lists the next-state probabilities from the corresponding current state. Starting certainly in $A$ means $p_0=(1,0)$, so</p>
<div class="math-block">$$p_1=p_0P=(1,0)\begin{bmatrix}0.8&0.2\\0.3&0.7\end{bmatrix}=(0.8,0.2).$$</div>
<p>For the next step, multiply this distribution by $P$ again. Each coordinate adds the two disjoint possible intermediate states:</p>
<div class="math-block">$$\begin{aligned}
\mathbb P(s_2=A)&=0.8(0.8)+0.2(0.3)=0.64+0.06=0.70,\\
\mathbb P(s_2=B)&=0.8(0.2)+0.2(0.7)=0.16+0.14=0.30.
\end{aligned}$$</div>
<p>Hence $p_2=(0.7,0.3)$, whose coordinates are nonnegative and sum to one. The products use conditional transition probabilities along each path, followed by addition across paths; they do not assume that consecutive states are independent.</p>
""", ["Explain the row convention and both matrix coordinates.", "Distinguish conditional path multiplication from independent states."])

add("#pr-extra-8", r"""
<p>A stationary distribution is unchanged by one transition. Write $p_*=(a,1-a)$ so its entries already sum to one. The first coordinate of $p_*P=p_*$ gives</p>
<div class="math-block">$$a=0.8a+0.3(1-a)=0.8a+0.3-0.3a=0.5a+0.3.$$</div>
<p>Subtract $0.5a$ from both sides: $0.5a=0.3$, hence $a=0.3/0.5=0.6$ and $1-a=0.4$. Both are valid probabilities. Check the second coordinate directly:</p>
<div class="math-block">$$0.6(0.2)+0.4(0.7)=0.12+0.28=0.4.$$</div>
<p>Therefore $p_*=(0.6,0.4)$. Stationarity is a claim about the distribution across possible trajectories. It does not freeze an individual trajectory: whenever it is in $A$, the next state is still $B$ with probability $0.2$, and whenever it is in $B$, it can move to $A$ with probability $0.3$.</p>
""", ["Show the full scalar equation and solve it.", "Check normalization and the unused coordinate; interpret stationarity pathwise."])

add("#pr-extra-9", r"""
<p>A Bernoulli variable with $p=0.2$ has mean $0.2$ and variance $p(1-p)=0.2(0.8)=0.16$. For $100$ independent draws, the covariances between different draws are zero, so</p>
<div class="math-block">$$\operatorname{Var}\!\left(\frac1{100}\sum_{i=1}^{100}Z_i\right)
=\frac1{100^2}\sum_{i=1}^{100}\operatorname{Var}(Z_i)
=\frac{100(0.16)}{100^2}=0.0016.$$</div>
<p>Let the $50$ genuinely independent draws in the second experiment be $W_1,\ldots,W_{50}$. Repeating each twice changes the recorded list, but its average simplifies:</p>
<div class="math-block">$$\frac{W_1+W_1+\cdots+W_{50}+W_{50}}{100}
=\frac2{100}\sum_{i=1}^{50}W_i=\frac1{50}\sum_{i=1}^{50}W_i.$$</div>
<p>Its variance is therefore $50(0.16)/50^2=0.0032$. Both averages have expectation $0.2$, but their standard deviations are $\sqrt{0.0016}=0.04$ and $\sqrt{0.0032}\approx0.05657$. The second variance is twice as large. Copies of the same draw are perfectly dependent; the independent sample sizes are $100$ and $50$, not $100$ in both cases.</p>
""", ["Derive the independent-average variance from a scaled sum.", "Name the distinct draws and simplify the duplicated average before computing precision."])

add("#pr-extra-10", r"""
<p>In $\mathcal N(\mu,\sigma^2)$, the second parameter is the variance. Here $\mu=10$, $\sigma^2=4$ and $\sigma=\sqrt4=2$. The standardized variable $Z=(X-10)/2$ has law $\mathcal N(0,1)$.</p>
<p>Because we divide by the positive number $2$, the inequality keeps its direction:</p>
<div class="math-block">$$X\le12\quad\Longleftrightarrow\quad
\frac{X-10}{2}\le\frac{12-10}{2}=1.$$</div>
<p>Thus $\mathbb P(X\le12)=\Phi(1)\approx0.8413$. For the interval, standardize both endpoints: $(8-10)/2=-1$ and $(12-10)/2=1$. Gaussian symmetry gives $\Phi(-1)=1-\Phi(1)$, so</p>
<div class="math-block">$$\mathbb P(8\le X\le12)=\Phi(1)-\Phi(-1)
=2\Phi(1)-1\approx2(0.8413)-1=0.6826.$$</div>
<p>The interval is one standard deviation on either side of the mean. Its coverage is about $68.3\%$, not $95\%$.</p>
""", ["Identify the square root of the variance explicitly.", "Transform both events and show the symmetry calculation."])

add("#pr-extra-11", r"""
<p>The independent Gaussian prior and measurement likelihood multiply. Their quadratic terms determine the posterior. With the observed $y=3$, ignore factors constant in $f$ and write the density as proportional to</p>
<div class="math-block">$$\exp\!\left[-\frac12\left(\frac{f^2}{4}+(3-f)^2\right)\right].$$</div>
<p>Expand and complete the square:</p>
<div class="math-block">$$\frac{f^2}{4}+(3-f)^2
=\frac54f^2-6f+9
=\frac54\left(f-\frac{12}5\right)^2+\frac95.$$</div>
<p>The constant $9/5$ changes only normalization. A Gaussian exponent has the form $(f-m)^2/s^2$, so the posterior mean is $m=12/5=2.4$ and its variance is $s^2=(5/4)^{-1}=4/5=0.8$. Equivalently, prior precision $1/4$ plus measurement precision $1$ gives $5/4$, and the mean is $(0/4+3)/(5/4)$.</p>
<p>A future reading is $f+\varepsilon_{\rm new}$, where the new noise has variance $1$ and is independent of the posterior offset uncertainty. Conditional on the existing observation, its variance is $4/5+1=9/5=1.8$. The mean remains $2.4$. The latent variance $0.8$ answers uncertainty about $f$; the larger predictive variance answers uncertainty about a new noisy reading.</p>
""", ["Derive the posterior by an explicit square completion.", "State the conditional independence used when adding future noise variance."])

add("#pr-extra-12", r"""
<p>A linear combination of a jointly Gaussian vector is Gaussian. For $S=h^\top X$ with $h=(1,1)^\top$, the mean is $h^\top(1,2)^\top=1+2=3$. The variance includes both off-diagonal covariance contributions:</p>
<div class="math-block">$$\operatorname{Var}(S)=h^\top\Sigma h
=1(1)1+1(0.5)1+1(0.5)1+1(4)1=6.$$</div>
<p>Thus $S\sim\mathcal N(3,6)$ and its standard deviation is $\sqrt6$. Standardization converts the requirement to</p>
<div class="math-block">$$\mathbb P(S\le b)=\Phi\!\left(\frac{b-3}{\sqrt6}\right)\ge0.95.$$</div>
<p>Since $\Phi$ is strictly increasing, this holds exactly when $(b-3)/\sqrt6\ge\Phi^{-1}(0.95)$. Multiplying by the positive $\sqrt6$ and adding $3$ gives the smallest threshold</p>
<div class="math-block">$$b_* = 3+\sqrt6\,\Phi^{-1}(0.95)\approx7.0291.$$</div>
<p>The supplied rounded quantile instead gives $3+1.64485\sqrt6\approx7.0290$. This is an estimate: $1.64485$ is below the exact quantile, so that substituted threshold is slightly below $b_*$ and does not meet the exact $0.95$ requirement. Use the exact expression when stating the guarantee. This is a one-sided upper threshold; the familiar $1.96$ is a rounded radius for a two-sided interval.</p>
""", ["Show every covariance term and invert the CDF inequality.", "Keep the existing exact-versus-rounded quantile qualification and explain its direction."])

add("#pr-extra-13", r"""
<p>Markov's inequality applies to a nonnegative random variable. One way to see the bound is that on the event $A=\{X\ge8\}$, the cost is at least $8$, while outside it the cost is still nonnegative. Therefore $\mathbb E[X]\ge8\mathbb P(A)$, and</p>
<div class="math-block">$$\mathbb P(X\ge8)\le\frac{\mathbb E[X]}8=\frac28=\frac14.$$</div>
<p>At the threshold $1$, the same argument yields $\mathbb P(X\ge1)\le2/1=2$. This remains a true inequality, but every probability also satisfies $\mathbb P(X\ge1)\le1$. Combining the two bounds gives $\mathbb P(X\ge1)\le\min(2,1)=1$.</p>
<p>The first calculation gives a useful upper limit; the second gives no restriction beyond the definition of probability. Neither is an estimate of the actual tail probability from a specified distribution.</p>
""", ["Explain why nonnegativity yields Markov's inequality.", "Combine the loose result with the universal probability bound."])

add("#pr-extra-14", r"""
<p>The observations are independent, bounded in $[0,1]$ and have the common mean $\mu$, so two-sided Hoeffding gives</p>
<div class="math-block">$$\mathbb P(|\bar X_N-\mu|\ge0.1)\le
2\exp[-2N(0.1)^2]=2e^{-0.02N}.$$</div>
<p>To make this failure bound at most $0.05$, solve the inequality rather than round a guessed sample size:</p>
<div class="math-block">$$\begin{aligned}
2e^{-0.02N}&\le0.05,\\
e^{-0.02N}&\le0.025=\frac1{40},\\
-0.02N&\le-\ln40,\\
N&\ge\frac{\ln40}{0.02}\approx184.44397.
\end{aligned}$$</div>
<p>The logarithm preserves the inequality because it is increasing on positive numbers; division by $-0.02$ reverses it. Since $N$ must be an integer, choose $N=185$. The bounds at $184$ and $185$ are approximately $0.05045$ and $0.04945$, confirming the rounding direction.</p>
<p>This is the smallest integer certified by this Hoeffding calculation. It does not assert that no smaller sample could work for a more specifically known law.</p>
""", ["Show all logarithm and inequality-direction steps.", "Check the two adjacent integer sizes and distinguish sufficient from necessary sample size."])

add("#pr-extra-15", r"""
<p>A uniform error on $[0,2]$ has mean $(0+2)/2=1$. Independence makes averaging reduce its random fluctuations, but it does not remove that mean: the average tends to $1$, not $0$.</p>
<p>The zero-mean sub-Gaussian condition asks for $\mathbb E[e^{\lambda\varepsilon}]\le e^{\lambda^2R^2/2}$ for every real $\lambda$. For the claimed $R=2$, there is a concrete contradiction. At $\lambda=1/4$, integrate the uniform density:</p>
<div class="math-block">$$\mathbb E[e^{\varepsilon/4}]
=\frac12\int_0^2e^{x/4}\,dx
=2(e^{1/2}-1)\approx1.29744,$$</div>
<p>whereas the proposed upper bound is $e^{(1/4)^2(2)^2/2}=e^{1/8}\approx1.13315$. The left side is larger. More generally, a nonzero mean produces a linear term $1+\lambda\mathbb E[\varepsilon]+O(\lambda^2)$ near zero, while the claimed bound has no linear term.</p>
<p>Center correctly with $\xi=\varepsilon-1$. Then $\mathbb E[\xi]=1-1=0$ and $\xi\in[-1,1]$. Hoeffding's lemma for a centered variable in $[a,b]$ gives $R=(b-a)/2$, hence $R=(1-(-1))/2=1$ here. The observation model becomes $y=f+1+\xi$: the bias $1$ must be included or corrected separately.</p>
""", ["Give a concrete MGF violation for the claimed parameter.", "Show the integration, centering and observation-model consequence."])

add("#pr-extra-16", r"""
<p>Let $F_i$ be the event that check $i$ fails. All three pass exactly on $(F_1\cup F_2\cup F_3)^c$: the complement of at least one failure.</p>
<p>The union bound follows because counting the probabilities separately can count outcomes that fail several checks more than once. It therefore gives an upper bound:</p>
<div class="math-block">$$\mathbb P(F_1\cup F_2\cup F_3)
\le\mathbb P(F_1)+\mathbb P(F_2)+\mathbb P(F_3)
\le0.01+0.01+0.01=0.03.$$</div>
<p>Taking a complement yields $\mathbb P(\text{all pass})=1-\mathbb P(\text{any failure})\ge1-0.03=0.97$.</p>
<p>No independence is needed. If passing events were independent, their probabilities could instead be multiplied, giving at least $0.99^3=0.970299$. That stronger bound uses an extra assumption; the supplied marginal bounds alone justify $0.97$.</p>
""", ["Identify the simultaneous event and its complement.", "Distinguish the union bound from the extra independent-product calculation."])

add("#pr-extra-17", r"""
<p>Let $F_i=\{|\bar X_{i,N}-\mu_i|\ge0.1\}$ for the ten means. A total failure budget $0.05$ shared equally gives $\delta_i=0.05/10=0.005$. Within each data set, its own independent observations lie in $[0,1]$, so Hoeffding applies:</p>
<div class="math-block">$$\mathbb P(F_i)\le2e^{-2N(0.1)^2}=2e^{-0.02N}.$$</div>
<p>Impose this bound separately for every $i$ and solve:</p>
<div class="math-block">$$2e^{-0.02N}\le0.005
\ \Longleftrightarrow\ e^{-0.02N}\le0.0025=\frac1{400}
\ \Longleftrightarrow\ N\ge\frac{\ln400}{0.02}\approx299.5732.$$</div>
<p>Round upward to $N=300$ observations per mean. The probability that at least one mean misses its target is then at most $\sum_{i=1}^{10}\delta_i=10(0.005)=0.05$, so all ten targets hold together with probability at least $0.95$.</p>
<p>Independence is used within each data set for Hoeffding, and not between data sets for the union bound. Giving each mean a pointwise failure budget $0.05$ would instead sum to $0.5$, providing only the lower bound $1-0.5=0.5$ for simultaneous success.</p>
""", ["Define the ten failure events and distinguish the two uses of dependence assumptions.", "Show the logarithmic sample-size calculation and the simultaneous complement."])

add("#pr-extra-18", r"""
<p>Write $F_t$ for failure at time $t$. For any finite $T$, the union bound and the supplied individual guarantees give $\mathbb P(\bigcup_{t=1}^T F_t)\le\sum_{t=1}^T\delta_t$. The reciprocal identity in the hint makes the sum explicit:</p>
<div class="math-block">$$\begin{aligned}
\sum_{t=1}^T\delta_t
&=0.05\sum_{t=1}^T\left(\frac1t-\frac1{t+1}\right)\\
&=0.05\left[(1-\tfrac12)+(\tfrac12-\tfrac13)+\cdots+
(\tfrac1T-\tfrac1{T+1})\right]\\
&=0.05\left(1-\frac1{T+1}\right).
\end{aligned}$$</div>
<p>The intermediate terms cancel. Letting $T$ grow gives total budget $0.05$. The finite unions increase to the event of any failure at any positive time, so the countable union bound gives $\mathbb P(\bigcup_{t=1}^\infty F_t)\le0.05$. Its complement, all statements holding at all times, has probability at least $0.95$.</p>
<p>A budget $0.05$ at every time does not justify the same conclusion: the sum through $T$ would be $0.05T$ and the infinite sum diverges. To see that this is a real gap, choose independent failures each of probability $0.05$. Then no failure through $T$ has probability $0.95^T\to0$, so an eventual failure has probability one. Independence is needed for that counterexample, not for the summable-budget guarantee.</p>
""", ["Write the telescoping cancellation and infinite-event limit.", "Separate an uninformative budget sum from the explicit independent-failure counterexample."])

add("#pr-extra-19", r"""
<p>Separate the already recorded sum from the next increment:</p>
<div class="math-block">$$S_{t+1}=S_t+\varepsilon_{t+1}.$$</div>
<p>At time $t$, the information $\mathcal F_t$ determines $S_t$, so conditioning leaves it unchanged. The next sign is independent of that past and still equally likely to be $-1$ or $1$; its conditional mean is $(-1)(1/2)+1(1/2)=0$. Hence</p>
<div class="math-block">$$\mathbb E[S_{t+1}\mid\mathcal F_t]
=S_t+\mathbb E[\varepsilon_{t+1}\mid\mathcal F_t]
=S_t+0=S_t.$$</div>
<p>Each $S_t$ is measurable from the first $t$ signs and integrable because $|S_t|\le t$. Together with the displayed conditional equality, these are the martingale conditions. A martingale need not remain constant: this walk changes by one on every step, while its expected next change given the past is zero.</p>
""", ["Compute the next sign's conditional mean from its two values.", "Check measurability and integrability as well as the conditional equality."])

add("#pr-extra-20", r"""
<p>The choice $a_t$ uses only $S_{t-1}$, so it is known from $\mathcal F_{t-1}$ before the new sign arrives. This is the predictability needed to take it outside the conditional expectation. Since the next fair sign has conditional mean zero,</p>
<div class="math-block">$$\mathbb E[D_t\mid\mathcal F_{t-1}]
=\mathbb E[a_t\varepsilon_t\mid\mathcal F_{t-1}]
=a_t\mathbb E[\varepsilon_t\mid\mathcal F_{t-1}]
=a_t(0)=0.$$</div>
<p>Given that past, $a_t$ is a fixed positive number, either $1$ or $2$, and $D_t$ takes values $-a_t,a_t$ with equal probabilities. Its conditional law is centered and supported in an interval of length $2a_t$. Conditional Hoeffding's lemma therefore gives</p>
<div class="math-block">$$\mathbb E[e^{\lambda D_t}\mid\mathcal F_{t-1}]
\le e^{\lambda^2a_t^2/2}\le e^{\lambda^2(2)^2/2}\qquad(\lambda\in\mathbb R).$$</div>
<p>The second inequality uses $a_t\le2$. Thus $a_t$ is a valid conditional parameter for that particular past, and the fixed choice $R=2$ works uniformly at every time. Adaptation can create dependence between increments; the argument uses predictable choices and a centered conditional law instead of independence of the $D_t$.</p>
""", ["State exactly why the multiplier can be taken outside conditioning.", "Derive the conditional interval length and uniform MGF bound."])

add("#pr-extra-21", r"""
<p>List both possible outcomes of the new sign. If $\varepsilon_t=1$, then $a_t=1$ and $D_t=1\cdot1=1$. If $\varepsilon_t=-1$, then $a_t=-1$ and $D_t=(-1)(-1)=1$. Thus $D_t=\varepsilon_t^2=1$ for every outcome.</p>
<p>A constant remains that constant after conditioning:</p>
<div class="math-block">$$\mathbb E[D_t\mid\mathcal F_{t-1}]=\mathbb E[1\mid\mathcal F_{t-1}]=1.$$</div>
<p>Its accumulated sum after $T$ steps is $T$, so it has positive deterministic drift. The failed step would be to write $\mathbb E[a_t\varepsilon_t\mid\mathcal F_{t-1}]=a_t\mathbb E[\varepsilon_t\mid\mathcal F_{t-1}]$. That requires $a_t$ to be determined by the past, but here it depends on the new sign itself.</p>
<p>Fairness gives mean zero for $\varepsilon_t$, not for every data-dependent transformation of it. In particular, the product of these dependent factors has mean $1$ even though each factor individually has mean zero.</p>
""", ["Enumerate both outcomes and compute the accumulated sum.", "Identify the missing past-measurability condition in the claimed proof."])

add("#pr-extra-22", r"""
<p>Entropy averages the negative logarithm of an outcome's probability over both outcomes. For a fair coin, use $\ln(1/2)=-\ln2$:</p>
<div class="math-block">$$H(1/2)=-\frac12\ln\frac12-\frac12\ln\frac12
=\frac12\ln2+\frac12\ln2=\ln2\approx0.693147\text{ nats}.$$</div>
<p>For success probability $1/4$, the failure probability is $3/4$, not zero. Substitute both probabilities:</p>
<div class="math-block">$$\begin{aligned}
H(1/4)&=-\frac14\ln\frac14-\frac34\ln\frac34\\
&\approx-\frac14(-1.386294)-\frac34(-0.287682)\\
&\approx0.346574+0.215762=0.562335\text{ nats}.
\end{aligned}$$</div>
<p>The biased coin has lower entropy: knowing its bias makes its result more predictable. Natural logarithms give nats; using base-two logarithms would give bits. The numerical values above are rounded evaluations of the exact expressions.</p>
""", ["Evaluate each entropy term with its sign and averaging weight.", "State the role of the second outcome and logarithm units."])

add("#pr-extra-23", r"""
<p>Both laws put positive mass on each outcome, so both KL directions are finite. Total variation compares coordinate differences symmetrically:</p>
<div class="math-block">$$\operatorname{TV}(p,q)=\frac12\left(|0.75-0.5|+|0.25-0.5|\right)
=\frac12(0.25+0.25)=0.25.$$</div>
<p>For KL, use the first law as the averaging weights and form its ratios to the second law:</p>
<div class="math-block">$$\begin{aligned}
D_{\rm KL}(p\|q)
&=0.75\ln\frac{0.75}{0.5}+0.25\ln\frac{0.25}{0.5}\\
&=0.75\ln1.5+0.25\ln0.5\\
&\approx0.304099-0.173287=0.130812\text{ nats}.
\end{aligned}$$</div>
<p>Reversing direction changes both ratios and weights:</p>
<div class="math-block">$$D_{\rm KL}(q\|p)=0.5\ln\frac{0.5}{0.75}+0.5\ln\frac{0.5}{0.25}
=0.5\ln\frac23+0.5\ln2
\approx-0.202733+0.346574=0.143841.$$</div>
<p>The two KL values differ, while TV is unchanged on reversal. This direction dependence is one reason KL is not a distance metric.</p>
""", ["Show ratios, weights and separate logarithmic contributions.", "Make clear why reversing KL is not just swapping a label."])

add("#pr-extra-24", r"""
<p>For $D_{\rm KL}(p\|q)$, the first outcome contributes $1\ln(1/0.5)=\ln2$. The second outcome has zero $p$-mass and contributes zero by the stated convention. Therefore</p>
<div class="math-block">$$D_{\rm KL}(p\|q)=\ln2\approx0.693147.$$</div>
<p>In the reverse direction, $q$ assigns positive mass $0.5$ to the second outcome but $p$ assigns zero. Its logarithmic ratio is infinite, so $D_{\rm KL}(q\|p)=+\infty$. This is a support mismatch, not a large finite rounding error.</p>
<p>Total variation stays finite because it uses absolute probability differences:</p>
<div class="math-block">$$\operatorname{TV}(p,q)=\frac12(|1-0.5|+|0-0.5|)
=\frac12(0.5+0.5)=0.5.$$</div>
<p>Pinsker can use the finite KL direction:</p>
<div class="math-block">$$0.5=\operatorname{TV}(p,q)\le
\sqrt{\frac{D_{\rm KL}(p\|q)}2}=\sqrt{\frac{\ln2}2}\approx0.588705.$$</div>
<p>This is a valid upper bound but does not reproduce the exact TV. Using the infinite reverse KL would give an infinite upper bound and no useful restriction.</p>
""", ["Treat zero mass and missing support separately.", "Substitute the finite KL into Pinsker and compare it with exact TV."])

add("#pr-extra-25", r"""
<p>First write the CDF, which includes all mass at or below the threshold:</p>
<div class="math-block">$$F_L(z)=
\begin{cases}
0,&z\lt0,\\
0.8,&0\le z\lt10,\\
0.95,&10\le z\lt100,\\
1,&100\le z.
\end{cases}$$</div>
<p>At level $0.8$, every threshold below $0$ has CDF zero, while $z=0$ reaches $0.8$. Thus the infimum in the definition is $\operatorname{VaR}_{0.8}(L)=0$.</p>
<p>At level $0.9$, the CDF remains $0.8$ until the jump at $10$, where it becomes $0.8+0.15=0.95$. Hence $\operatorname{VaR}_{0.9}(L)=10$. At level $0.95$, the same threshold already satisfies the non-strict condition $F_L(10)\ge0.95$, giving $\operatorname{VaR}_{0.95}(L)=10$ as well.</p>
<p>The equality case matters at an atom. VaR $10$ at level $0.95$ still leaves the $0.05$ probability of loss $100$ above that threshold; it is not a statement that the loss cannot exceed $10$.</p>
""", ["Write the full step-function CDF.", "Justify each infimum and preserve the equality-at-an-atom convention."])

add("#pr-extra-26", r"""
<p>The worst $10\%$ means selecting probability mass $1-0.9=0.1$ from the highest losses downward. Use all the $0.05$ mass at loss $100$. That leaves $0.1-0.05=0.05$ mass to take from the loss-$10$ atom, which has total mass $0.15$.</p>
<p>Only one third of that atom is needed. Divide the loss-weighted selected mass by the selected mass:</p>
<div class="math-block">$$\operatorname{CVaR}_{0.9}(L)=
\frac{0.05(100)+0.05(10)}{0.1}
=\frac{5+0.5}{0.1}=55.$$</div>
<p>The full expectation instead includes every outcome with its original probability:</p>
<div class="math-block">$$\mathbb E[L]=0.8(0)+0.15(10)+0.05(100)=0+1.5+5=6.5.$$</div>
<p>The event $L\ge10$ contains $0.15+0.05=0.2$ mass. Its conditional mean is</p>
<div class="math-block">$$\mathbb E[L\mid L\ge10]
=\frac{0.15(10)+0.05(100)}{0.2}=\frac{6.5}{0.2}=32.5.$$</div>
<p>This conditions on the worst $20\%$, rather than selecting exactly the worst $10\%$. Atoms at VaR must be split when necessary; using the entire event $L\ge\operatorname{VaR}_{0.9}$ would give the wrong CVaR here.</p>
""", ["Explain how much probability mass remains after the rare worst loss.", "Compute all three averages with their different denominators."])

add("#pr-extra-27", r"""
<p>Expand the expectation into the three possible losses:</p>
<div class="math-block">$$g(\nu)=\nu+10\left[0.8(0-\nu)^+
+0.15(10-\nu)^++0.05(100-\nu)^+\right].$$</div>
<p>On each open interval, we know which positive parts are active. Substitute those expressions and simplify:</p>
<div class="math-block">$$g(\nu)=
\begin{cases}
\nu+10(6.5-\nu)=65-9\nu,&\nu\lt0,\\
\nu+10(6.5-0.2\nu)=65-\nu,&0\lt\nu\lt10,\\
\nu+10(5-0.05\nu)=50+0.5\nu,&10\lt\nu\lt100,\\
\nu,&100\lt\nu.
\end{cases}$$</div>
<p>For example, on $(0,10)$ only losses $10$ and $100$ contribute, giving $0.15(10-\nu)+0.05(100-\nu)=6.5-0.2\nu$. The four slopes are therefore $-9,-1,0.5,1$. The positive-part function is continuous, so these decreasing pieces lead up to $10$ and the increasing pieces start after $10$.</p>
<p>The minimum occurs at that kink. Direct substitution avoids differentiating where the derivative does not exist:</p>
<div class="math-block">$$\mathbb E[(L-10)^+]=0.8(0)+0.15(0)+0.05(90)=4.5,\qquad
g(10)=10+10(4.5)=55.$$</div>
<p>This agrees with the preceding split-tail CVaR. A kink can be a minimizer because the slope changes from negative to positive.</p>
""", ["Derive every piece of the objective, not just its slopes.", "Use continuity and the sign change to justify the global minimum at the kink."])

add("#pr-extra-28", r"""
<p>For a specified pair of failing runs, independence gives probability $0.1^2(0.9)^2=0.01(0.81)=0.0081$: both selected runs fail and both others pass.</p>
<p>There are $\binom42=4!/(2!2!)=6$ different choices of the pair. Their exact-two-failure events are disjoint, so</p>
<div class="math-block">$$\mathbb P(\text{exactly two failures})=6(0.0081)=0.0486.$$</div>
<p>For at least one failure, taking a complement is shorter than adding all the possible counts. No failure means that all four runs pass, with probability $0.9^4=0.6561$. Therefore</p>
<div class="math-block">$$\mathbb P(\text{at least one failure})=1-0.9^4=1-0.6561=0.3439.$$</div>
<p>Independence justifies multiplying run probabilities. Disjointness justifies adding the six patterns; these are two distinct steps in the calculation.</p>
""", ["Show the binomial coefficient and probability of one pattern.", "Distinguish multiplication by independence from addition over disjoint patterns."])

add("#pr-extra-29", r"""
<p>For a fixed failure probability $p$, independence gives probability $(1-p)^{100}$ of seeing zero failures. The one-sided $95\%$ upper limit puts this observed extreme outcome at the boundary probability $0.05$:</p>
<div class="math-block">$$\begin{aligned}
(1-p_U)^{100}&=0.05,\\
1-p_U&=0.05^{1/100},\\
p_U&=1-0.05^{1/100}
=1-\exp\!\left(\frac{\ln0.05}{100}\right)
\approx0.029513.
\end{aligned}$$</div>
<p>The positive hundredth root is the relevant one because $1-p_U$ is a probability. If a proposed true $p$ were larger than this limit, then $1-p$ would be smaller and observing zero failures would have probability below $0.05$. Inverting these binomial-tail tests gives the upper confidence-limit procedure.</p>
<p>The confidence statement concerns that procedure over repeated random data sets: its reported upper limit covers a fixed true $p$ with probability at least $0.95$. After this particular data set, it is not a posterior probability distribution for $p$. In particular, the observed absence of failures permits small positive failure rates and does not establish $p=0$.</p>
""", ["Solve the root equation and show its numerical evaluation.", "Explain the test inversion and distinguish fixed parameters from random confidence limits."])

add("#pr-extra-30", r"""
<p>Let $R$ denote the future score's rank among all $20$ scores, counted from the smallest. With no ties, exactly one score occupies each rank. Exchangeability says the future label is equally likely to be any of those scores, so $\mathbb P(R=r)=1/20$ for every $r=1,\ldots,20$.</p>
<p>Now compare an overall rank with the calibration threshold. If $R\le18$, at most $17$ calibration scores are smaller than the future score, so the $18$th calibration score is above it. If $R\ge19$, at least $18$ calibration scores are smaller, so the future score exceeds that threshold. Thus acceptance is exactly the event $R\le18$:</p>
<div class="math-block">$$\mathbb P(\text{accept})=\sum_{r=1}^{18}\mathbb P(R=r)
=18\left(\frac1{20}\right)=0.9.$$</div>
<p>This probability averages over the random calibration scores and the future point. It does not condition on a particular subgroup or on the calibration set we happened to obtain. To see why an average does not fix subgroup values, two equally common groups with acceptance probabilities $0.8$ and $1$ would give $(0.8+1)/2=0.9$ overall. The same marginal target is compatible with undercoverage in one group.</p>
<p>The no-ties assumption makes the rank equivalence exact; ties would require an additional tie-handling argument rather than automatically reusing this calculation.</p>
""", ["Prove uniform ranks from exchangeability and the acceptance/rank equivalence.", "Separate marginal, subgroup and fixed-calibration coverage."])

add("#book-c-b1", r"""
<p>Keep $F$ for a fault and $A$ for an alarm. The new base rate is $\mathbb P(F)=0.01$, while the sensor still has $\mathbb P(A\mid F)=0.90$ and $\mathbb P(A\mid F^c)=0.08$. Compute the two disjoint alarm routes:</p>
<div class="math-block">$$\mathbb P(F\cap A)=0.01(0.90)=0.009,\qquad
\mathbb P(F^c\cap A)=0.99(0.08)=0.0792.$$</div>
<p>Therefore $\mathbb P(A)=0.009+0.0792=0.0882$ and</p>
<div class="math-block">$$\mathbb P(F\mid A)=\frac{0.009}{0.0882}
=\frac{90}{882}=\frac5{49}\approx0.10204.$$</div>
<p>Inspection costs $6$ units and release after information $I$ costs $30\mathbb P(F\mid I)$. After an alarm, release costs $30(5/49)=150/49\approx3.0612$, below $6$, so an alarm should no longer trigger inspection in this expected-cost model.</p>
<p>Check silence as well. Missed faults have probability $0.01(0.10)=0.001$, and silence has probability $1-0.0882=0.9118$. Thus $\mathbb P(F\mid A^c)=0.001/0.9118\approx0.001097$, also below the inspection threshold $6/30=0.20$. Release is preferred in both information states.</p>
<p>Always releasing costs $30(0.01)=0.30$ units per package. Keeping the old inspect-on-alarm rule costs $6(0.0882)+30(0.001)=0.5292+0.03=0.5592$: inspection cost on alarms plus jam cost on missed faults. The unchanged rule is more expensive after the base-rate change. This comparison relies on the stated costs and perfect-inspection model; it does not promise that every released package is sound.</p>
""", ["Recompute both joint alarm routes and simplify Bayes' fraction.", "Compare actions after both outcomes and break the old rule's cost into its two sources."])

add("#book-c-b2", r"""
<p>Condition on the two calibration readings from example 2. Their posterior is $\theta\mid\text{data}\sim\mathcal N(m,s^2)$ with $m=7/6$ mm and $s^2=2/3\ {\rm mm}^2$. Subtracting $m$ centers the residual offset: $\theta-m$ has mean zero and variance $2/3$.</p>
<p>A corrected new reading has total error $e=\theta-m+\varepsilon_{\rm new}$. The fresh noise is independent of the offset and calibration data, so these two terms remain independent conditional on those data. A sum of independent Gaussian terms is Gaussian, with</p>
<div class="math-block">$$\mathbb E[e\mid\text{data}]=0+0=0,\qquad
\operatorname{Var}(e\mid\text{data})=\frac23+1=\frac53\ {\rm mm}^2.$$</div>
<p>The predictive standard deviation is $\sqrt{5/3}\approx1.2910$ mm. Standardize both sides of the tolerance interval:</p>
<div class="math-block">$$\mathbb P(|e|\le2\mid\text{data})
=\mathbb P\!\left(-\frac2{\sqrt{5/3}}\le Z\le\frac2{\sqrt{5/3}}\right)
=2\Phi\!\left(\frac2{\sqrt{5/3}}\right)-1\approx0.87866,$$</div>
<p>where $Z\sim\mathcal N(0,1)$ and the standardized upper endpoint is about $1.54919$. This is below $0.98$. The earlier probability $0.98569$ concerned only $\theta-m$, not a new noisy measurement. Mean correction removes the systematic center, while posterior offset uncertainty and fresh measurement noise still contribute spread.</p>
""", ["State the conditioning and why independence survives it.", "Identify the total-error Gaussian law and standardize both tolerance endpoints with units."])

add("#book-c-b3", r"""
<p>Keep the correction $m$ determined by the existing calibration data, and condition on those data. Put $U=\theta-m$, so $\operatorname{Var}(U)=2/3\ {\rm mm}^2$. Reading $i$ has error $e_i=U+\varepsilon_i$: the same $U$ occurs in every reading.</p>
<p>Averaging $n$ readings gives</p>
<div class="math-block">$$\bar e_n=\frac1n\sum_{i=1}^n(U+\varepsilon_i)
=\frac{nU}{n}+\frac1n\sum_{i=1}^n\varepsilon_i
=U+\frac1n\sum_{i=1}^n\varepsilon_i.$$</div>
<p>The new noises are mutually independent, independent of $U$, and each have variance $1$. Thus their average has variance $n/n^2=1/n$ and zero covariance with $U$:</p>
<div class="math-block">$$\operatorname{Var}(\bar e_n)=\frac23+\frac1n,\qquad
\operatorname{Var}(\bar e_{100})=\frac23+\frac1{100}
=\frac{200+3}{300}=\frac{203}{300}\approx0.67667\ {\rm mm}^2.$$</div>
<p>As $n\to\infty$, $1/n\to0$, leaving variance $2/3$ and standard deviation $\sqrt{2/3}\approx0.8165$ mm. More repeated readings reduce fresh noise, but the common offset does not average away.</p>
<p>For $i\ne j$, independence of the fresh noises gives $\operatorname{Cov}(e_i,e_j)=\operatorname{Var}(U)=2/3$. The usual division of a single reading's variance $5/3$ by $n$ would discard those cross-covariances. Reducing this floor requires improved calibration of the shared offset, rather than treating copies of the same offset uncertainty as independent.</p>
""", ["Write the shared offset through the averaging algebra.", "Derive the covariance between readings and the resulting variance floor."])

add("#book-c-b4", r"""
<p>Let $E_i$ denote an escaped fault on package $i$, with $\mathbb P(E_i)=q$. Any escaped fault in the batch is the union $\bigcup_{i=1}^{50}E_i$. Without an independence assumption, the union bound gives</p>
<div class="math-block">$$\mathbb P(\text{any escape})\le\sum_{i=1}^{50}\mathbb P(E_i)=50q.$$</div>
<p>It is sufficient to require $50q\le0.02$, or $q\le0.02/50=0.0004$. This is a sufficient allowance valid under arbitrary dependence.</p>
<p>With independent escapes of equal probability, no escape has exact probability $(1-q)^{50}$. Solve the exact batch requirement:</p>
<div class="math-block">$$\begin{aligned}
1-(1-q)^{50}&\le0.02,\\
(1-q)^{50}&\ge0.98,\\
1-q&\ge0.98^{1/50},\\
q&\le1-0.98^{1/50}\approx0.000403973.
\end{aligned}$$</div>
<p>The positive root preserves order on $[0,1]$. The exact independent allowance is slightly larger because the union bound can overcount outcomes with several escapes.</p>
<p>Example 1's $q=0.004$ exceeds both allowances. The union bound would only certify the much larger bound $50(0.004)=0.20$; under independence, the actual batch probability is $1-0.996^{50}\approx0.18160$, above $0.02$. These calculations start from assumed per-package rates. They are not statistical confidence limits inferred from observing a batch.</p>
""", ["Define the batch event and derive the dependence-free sufficient allowance.", "Solve the independent inequality in order and distinguish an upper bound from an actual probability."])

add("::exercise-38", r"""
<p><strong>(a)</strong> Let $I_i$ be $1$ when episode $i$ contains at least one violation and $0$ otherwise. For independent episodes with a common violation probability $p$, these are Bernoulli variables and the sample proportion estimates $p$:</p>
<div class="math-block">$$\hat p=\frac1{200}\sum_{i=1}^{200}I_i=\frac{14}{200}=0.07.$$</div>
<p>The true sampling variance of this average is $p(1-p)/200$. Replacing the unknown $p$ by $\hat p$ gives the estimated standard error</p>
<div class="math-block">$$\widehat{\mathrm{SE}}=
\sqrt{\frac{0.07(1-0.07)}{200}}
=\sqrt{\frac{0.07(0.93)}{200}}
=\sqrt{0.0003255}\approx0.01804.$$</div>
<p><strong>(b)</strong> The normal approximation uses about $1.96$ standard errors on either side. The half-width is $1.96(0.0180416)\approx0.0353616$, giving</p>
<div class="math-block">$$0.07\pm0.0353616
\approx[0.0346384,\,0.1053616]\approx[0.035,\,0.105].$$</div>
<p>These are approximate sampling-based confidence limits, not an exact finite-sample interval or a posterior interval for a random $p$.</p>
<p><strong>(c)</strong> Zero observed failures gives $\hat p=0$ and hence a plug-in standard error of zero. That boundary estimate does not establish certainty: positive true rates can still produce a clean sample. For any fixed $p$, the probability of $200$ clean independent episodes is $(1-p)^{200}$. The exact one-sided upper limit solves</p>
<div class="math-block">$$ (1-p_U)^{200}=0.05,\qquad
p_U=1-0.05^{1/200}
=1-\exp\!\left(\frac{\ln0.05}{200}\right)\approx0.014867.$$</div>
<p>This is the one-sided Clopper–Pearson limit. The approximation $-\ln0.05\approx3$ explains the rule of three, $p_U\approx3/200=0.015$. The resulting confidence procedure covers the fixed rate in at least $95\%$ of repeated samples; zero failures in this sample does not prove a zero population rate.</p>
""", ["Derive the standard error from Bernoulli indicators and show unrounded interval limits.", "Explain the boundary failure of the plug-in estimate and solve the exact confidence-limit equation."])

add("::exercise-39", r"""
<p><strong>(a)</strong> Let $C$ mean a change and $A$ an alarm. The two joint alarm routes are $\mathbb P(C\cap A)=0.02(0.9)=0.018$ and $\mathbb P(C^c\cap A)=0.98(0.01)=0.0098$. Add them before conditioning:</p>
<div class="math-block">$$\mathbb P(C\mid A)=\frac{0.018}{0.018+0.0098}
=\frac{0.018}{0.0278}=\frac{90}{139}\approx0.647.$$</div>
<p>The false-alarm fraction among alarms is consequently $49/139\approx0.353$, about one in three. Sensitivity and posterior change probability have different denominators.</p>
<p><strong>(b)</strong> With no change, define a false-alarm indicator at each step. Linearity of expectation gives an expected count $500(0.01)=5$, even without independence. Independence is needed for the next product: no false alarm has probability $0.99^{500}\approx0.0065705$. Thus</p>
<div class="math-block">$$\mathbb P(\text{at least one false alarm})=1-0.99^{500}\approx0.99343.$$</div>
<p><strong>(c)</strong> To cover any dependence, allocate the total failure budget equally: $\alpha=0.05/500=10^{-4}$. Then the union bound is $500\alpha=0.05$.</p>
<p>For a genuinely standard Gaussian null residual $r_t$, the two-sided alarm $|r_t|\gt q$ has probability $2[1-\Phi(q)]$. Set this to $\alpha$ and invert:</p>
<div class="math-block">$$2[1-\Phi(q)]=10^{-4},\qquad
\Phi(q)=1-5\cdot10^{-5},\qquad
q=\Phi^{-1}(0.99995)\approx3.890591886.$$</div>
<p>Use that exact quantile or the conservative numerical threshold $3.89060$. The displayed $3.89$ is an approximation rounded downward, so using it literally gives a per-step tail strictly larger than $10^{-4}$. The union guarantee requires the stated Gaussian residual law at each null-model step; independence between steps is unnecessary.</p>
""", ["Show both alarm routes and separate expectation from an independent product.", "Derive the two-sided quantile equation and preserve its conservative-rounding requirement."])

add("::exercise-40", r"""
<p><strong>(a)</strong> The four independent measurement noises each have variance $0.25$, so their average has variance $4(0.25)/4^2=0.25/4=0.0625=1/16$. Its precision is the reciprocal, $16$. The prior variance is $1$, hence prior precision $1$.</p>
<p>For independent Gaussian observations of the same $f$, precisions add and the mean is precision weighted:</p>
<div class="math-block">$$s^2=(1+16)^{-1}=\frac1{17},\qquad
m=\frac{1(0)+16(0.9)}{17}=\frac{14.4}{17}=\frac{72}{85}.$$</div>
<p>Thus $f\mid\text{data}\sim\mathcal N(72/85,1/17)$, with mean about $0.847059$, variance about $0.058824$, and standard deviation $s=1/\sqrt{17}\approx0.242536$. Each precision is inverse variance, not inverse standard deviation.</p>
<p><strong>(b)</strong> Standardize the safety threshold using this posterior:</p>
<div class="math-block">$$\mathbb P(f\lt0.5\mid\text{data})
=\Phi\!\left(\frac{0.5-72/85}{1/\sqrt{17}}\right)
=\Phi(-1.430960\ldots)\approx0.07622.$$</div>
<p><strong>(c)</strong> Evaluate the proposed lower bound before comparing it with $0.3$:</p>
<div class="math-block">$$m-2s=\frac{72}{85}-\frac2{\sqrt{17}}
\approx0.847059-0.485071=0.361988\gt0.3.$$</div>
<p>Therefore the $m-2s$ lower-bound rule certifies the proposed threshold under this posterior model. That lower bound fails exactly when $f\lt m-2s$, or $(f-m)/s\lt-2$, with posterior probability $\Phi(-2)\approx0.02275\approx0.023$. This is the failure probability of the displayed lower bound, rather than the probability of $f\lt0.3$. It is a Bayesian, model-dependent statement for this decision; multiple decisions need their joint failure event and risk allocation.</p>
""", ["Explain variance reduction of the measurement average before precision addition.", "Compute the standardized tail and distinguish lower-bound failure from target-threshold failure."])

add("::exercise-41", r"""
<p><strong>(a)</strong> For $0\le X\le1$, we have $X^2\le X$. With mean $m$, this yields</p>
<div class="math-block">$$\operatorname{Var}(X)=\mathbb E[X^2]-m^2
\le m-m^2=\frac14-(m-\tfrac12)^2\le\frac14.$$</div>
<p>Independence gives $\operatorname{Var}(\bar X_N)\le1/(4N)$. Chebyshev bounds the failure of the strict accuracy requirement by</p>
<div class="math-block">$$\mathbb P(|\bar X_N-m|\ge0.05)
\le\frac{1}{4N(0.05)^2}=\frac{100}{N}.$$</div>
<p>Require $100/N\le0.01$, so $N\ge10000$. Hoeffding instead gives $2e^{-2N(0.05)^2}=2e^{-0.005N}$. Solving $2e^{-0.005N}\le0.01$ gives $N\ge\ln(200)/0.005\approx1059.6635$, hence $N=1060$. These are sufficient sizes from the two bounds, using independent samples with the stated mean and range.</p>
<p><strong>(b)</strong> A uniform error on $[-0.2,0.2]$ is centered. Hoeffding's lemma supplies $R=(0.2-(-0.2))/2=0.2$. Its variance is $(0.4)^2/12=1/75$, so its standard deviation is $\sigma=0.4/\sqrt{12}=0.2/\sqrt3\approx0.11547$.</p>
<p>The sharper claim in the section's table, that the smallest valid $R$ for this uniform law equals $\sigma$, can be checked explicitly. For a uniform $U$ on $[-a,a]$, integration gives the MGF $\mathbb E[e^{tU}]=\sinh(at)/(at)$, with value $1$ at $t=0$. Its power series obeys</p>
<div class="math-block">$$\frac{\sinh(at)}{at}
=\sum_{j=0}^\infty\frac{(a^2t^2)^j}{(2j+1)!}
\le\sum_{j=0}^\infty\frac{(a^2t^2/6)^j}{j!}
=e^{a^2t^2/6}.$$</div>
<p>The coefficient inequality uses $(2j+1)!\ge6^j j!$: starting at $j=0$, each next factor $(2j+2)(2j+3)$ is at least $6(j+1)$. All series terms are nonnegative. Thus $R=a/\sqrt3$ works, since $a^2t^2/6=R^2t^2/2$. No smaller value works: the second-order MGF terms are $1+a^2t^2/6+\cdots$ and $1+R^2t^2/2+\cdots$, requiring $R^2\ge a^2/3$. At $a=0.2$, Hoeffding's $0.2$ is conservative by the factor $\sqrt3$.</p>
<p><strong>(c)</strong> A uniform error on $[0,0.2]$ has mean $0.1$, so it does not satisfy the uncentered zero-mean MGF condition used above. Write it as $0.1+\xi$, where $\xi$ is centered and uniform on $[-0.1,0.1]$. The bias must still appear in the observation model or be corrected separately; increasing a noise scale cannot make that mean vanish.</p>
""", ["Derive the worst-case variance and both sample-size inequalities.", "Supply the missing uniform-MGF proof of the optimal parameter and its variance lower bound.", "Explain centering the biased noise without erasing the model offset."])

add("::exercise-42", r"""
<p><strong>(a)</strong> All coordinates of $p$ and $q$ are positive. Using natural logarithms and the first law as weights,</p>
<div class="math-block">$$\begin{aligned}
\mathrm{KL}(p\|q)
&=0.6\ln\frac{0.6}{0.4}+0.3\ln\frac{0.3}{0.4}+0.1\ln\frac{0.1}{0.2}\\
&=0.6\ln1.5+0.3\ln0.75+0.1\ln0.5\\
&\approx0.243279-0.086305-0.069315=0.087660,\\
\mathrm{KL}(q\|p)
&=0.4\ln\frac23+0.4\ln\frac43+0.2\ln2\\
&\approx-0.162186+0.115073+0.138629=0.091516.
\end{aligned}$$</div>
<p>Both are in nats. Total variation is $d_{\rm TV}(p,q)=\tfrac12(|0.6-0.4|+|0.3-0.4|+|0.1-0.2|)=\tfrac12(0.2+0.1+0.1)=0.2$.</p>
<p><strong>(b)</strong> TV is symmetric, so Pinsker can use either KL direction. Evaluating the bounds from the exact expressions gives</p>
<div class="math-block">$$0.2\le\sqrt{\mathrm{KL}(p\|q)/2}\approx0.20936,\qquad
0.2\le\sqrt{\mathrm{KL}(q\|p)/2}\approx0.21391.$$</div>
<p>Both inequalities hold, although their upper bounds differ.</p>
<p><strong>(c)</strong> The third coordinate contributes $0.1\ln(0.1/0)$ to $\mathrm{KL}(p\|q')$, hence this direction is infinite. In the reverse direction, the zero $q'$-weight contributes zero:</p>
<div class="math-block">$$\mathrm{KL}(q'\|p)=0.5\ln\frac{0.5}{0.6}
+0.5\ln\frac{0.5}{0.3}
=0.5\ln\frac56+0.5\ln\frac53\approx0.164.$$</div>
<p>A finite constraint $\mathrm{KL}(\text{new}\|\text{old})\le\epsilon$ therefore forbids positive new-policy mass on an action with zero old-policy mass. The direction of the trust-region KL determines this support restriction.</p>
""", ["Show each logarithmic ratio and weighted contribution.", "Use both finite KL directions in Pinsker and explain the support restriction of the chosen trust-region direction."])

add("::exercise-43", r"""
<p><strong>(a)</strong> Weight each possible cost by its probability:</p>
<div class="math-block">$$\mathbb E[Z]=0.8(0)+0.15(2)+0.05(10)=0.3+0.5=0.8,\qquad
\mathbb P(Z\gt0)=0.15+0.05=0.2.$$</div>
<p>The CDF has $F(0)=0.8$ and $F(2)=0.95$, so the first threshold reaching $0.9$ is $\operatorname{VaR}_{0.9}(Z)=2$. The worst $10\%$ of mass uses all $0.05$ at cost $10$ and another $0.05$ from the cost-$2$ atom:</p>
<div class="math-block">$$\operatorname{CVaR}_{0.9}(Z)=\frac{0.05(10)+0.05(2)}{0.1}
=\frac{0.5+0.1}{0.1}=6.$$</div>
<p>In the Rockafellar–Uryasev formula, the multiplier is $1/(1-0.9)=10$. At $\nu=2$, only cost $10$ has positive excess, so</p>
<div class="math-block">$$\nu+\frac{\mathbb E[(Z-\nu)^+]}{0.1}
=2+\frac{0.05(10-2)}{0.1}=2+4=6.$$</div>
<p><strong>(b)</strong> The second moment is $0.15(2^2)+0.05(10^2)=0.6+5=5.6$. Thus the variance is $5.6-0.8^2=4.96$ and $\sigma=\sqrt{4.96}\approx2.227106$.</p>
<p>For the Gaussian comparison law, let $q=\Phi^{-1}(0.9)$ and let $\varphi$ be the standard-normal density. Its upper $10\%$ corresponds to a standard-normal variable $W\ge q$. Since $\varphi'(w)=-w\varphi(w)$, integration gives $\int_q^\infty w\varphi(w)\,dw=\varphi(q)$. Dividing by the tail probability $0.1$ yields</p>
<div class="math-block">$$\operatorname{CVaR}_{0.9}(\text{Gaussian})
=0.8+\sqrt{4.96}\frac{\varphi(\Phi^{-1}(0.9))}{0.1}
\approx0.8+2.227106(1.754983)\approx4.71.$$</div>
<p>Here $q\approx1.2816$ and $\varphi(q)\approx0.175498$; these and the final value are approximations. Matching the mean and variance does not match the tail law: the Gaussian result is about $1.3$ below the actual discrete CVaR $6$.</p>
<p><strong>(c)</strong> The actual mean constraint holds because $0.8\le1$, and the chance constraint holds because $0.2\le0.25$. The actual CVaR constraint fails because $6\gt5$. Using the Gaussian shortcut would incorrectly accept this last constraint, since its approximate $4.71$ is below $5$.</p>
""", ["Derive the atom-splitting and optimization calculations separately.", "Compute the variance and derive the Gaussian tail-average formula by integrating its density.", "Judge each constraint using the actual discrete law."])

add("::exercise-44", r"""
<p><strong>(a)</strong> Split conformal uses $k=\lceil(n+1)(1-\alpha)\rceil$. Here $n=19$ and $\alpha=0.1$, so $k=\lceil20(0.9)\rceil=18$. The threshold is the $18$th smallest of the $19$ calibration scores, their second largest. Continuity prevents ties, and the future score has uniform rank among all $20$ scores. Acceptance is equivalent to rank at most $18$, giving marginal coverage $18/20=0.9$.</p>
<p><strong>(b)</strong> Fix a realized calibration set. Its true conditional coverage is $C=F(S_{(18)})$, because a fresh independent score has CDF $F$. Across random calibration sets, the probability integral transform makes the $19$ values $F(S_i)$ independent uniforms. Since $F$ preserves their order, $C$ is their $18$th order statistic.</p>
<p>For $0\le c\le1$, the event $C\le c$ means at least $18$ of these $19$ uniforms lie below $c$. Count the cases of exactly $18$ and all $19$:</p>
<div class="math-block">$$\mathbb P(C\le c)=\binom{19}{18}c^{18}(1-c)+c^{19}
=19c^{18}-18c^{19}.$$</div>
<p>Differentiating gives density $342c^{17}(1-c)$ on $[0,1]$, the Beta$(18,2)$ law. Its first two moments can be obtained by elementary integration:</p>
<div class="math-block">$$\begin{aligned}
\mathbb E[C]&=342\int_0^1(c^{18}-c^{19})\,dc
=342\left(\frac1{19}-\frac1{20}\right)=\frac9{10},\\
\mathbb E[C^2]&=342\int_0^1(c^{19}-c^{20})\,dc
=342\left(\frac1{20}-\frac1{21}\right)=\frac{57}{70}.
\end{aligned}$$</div>
<p>Thus $\operatorname{Var}(C)=57/70-(9/10)^2=3/700\approx0.004286$, and its standard deviation is $\sqrt{3/700}\approx0.06547$. Substituting $c=0.8$ into the CDF gives</p>
<div class="math-block">$$\mathbb P(C\lt0.8)=19(0.8)^{18}(0.2)+(0.8)^{19}
\approx0.08287\approx0.083.$$</div>
<p>The strict inequality has the same probability because this law is continuous. About one calibration set in twelve has true conditional coverage below $0.8$, despite the correct $0.9$ marginal coverage.</p>
<p><strong>(c)</strong> Given the calibration set, its $m=2000$ fresh test acceptances are independent Bernoulli variables with probability $C$. Their measured fraction $\hat C$ therefore satisfies $\mathbb E[\hat C\mid C]=C$ and $\operatorname{Var}(\hat C\mid C)=C(1-C)/2000$. Across both calibration and test randomness, total variance gives</p>
<div class="math-block">$$\operatorname{Var}(\hat C)=\operatorname{Var}(C)
+\frac{\mathbb E[C(1-C)]}{2000}.$$</div>
<p>The remaining expectation is $\mathbb E[C]-\mathbb E[C^2]=9/10-57/70=3/35$. Therefore</p>
<div class="math-block">$$\operatorname{Var}(\hat C)=\frac3{700}+\frac{3/35}{2000}
=\frac{300}{70000}+\frac3{70000}=\frac{303}{70000},\qquad
\operatorname{SD}(\hat C)=\sqrt{\frac{303}{70000}}\approx0.0658.$$</div>
<p>The test-set contribution is only $1\%$ of the calibration variance. More test points estimate a fixed set's coverage more accurately, but do not remove the spread caused by using only $19$ calibration scores. The Beta calculation uses the supplied i.i.d. continuous score law; exchangeability alone would justify the marginal rank argument, but not this conditional-coverage law.</p>
""", ["Derive the order-statistic CDF, Beta density and moments by explicit counting and integration.", "Compute the lower-coverage probability and total variance over calibration and test randomness.", "Keep the i.i.d.-versus-exchangeability distinction explicit."])


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    baseline = json.loads(BASELINE.read_text())
    rows = baseline["exercises"]
    assert len(rows) == 44
    retained = {"primer-probability.html#pr-ready-1", "primer-probability.html#pr-ready-2"}
    assert set(AUTHORED) | retained == {row["inventory_key"] for row in rows}
    assert not set(AUTHORED) & retained
    drafts = []
    for row in rows:
        key = row["inventory_key"]
        original = row["solution"]["html"]
        assert digest(original.encode()) == row["solution"]["sha256"]
        if key in retained:
            replacement = original
            improvements = []
            rationale = (
                "Already adequate for this one-step readiness question: the complete original solution "
                "states the method, computes the numerical result, explains why it works, and interprets it. "
                "C.R1 identifies the complement, disjoint partition and trajectory scope. "
                "C.R2 supplies both a four-case calculation and the weighted calculation and explains the erroneous unweighted sum."
            )
            decision = "retain"
        else:
            replacement = AUTHORED[key]["replacement_html"]
            improvements = AUTHORED[key]["specific_improvements"]
            rationale = "The original final facts are correct, but the baseline student needs the following problem-specific intermediate reasoning: " + " ".join(improvements)
            decision = "replace"
        drafts.append({
            "inventory_key": key, "source_file": row["source_file"],
            "authoring_file": row["authoring_file"], "ordinal": row["ordinal"],
            "anchor": row["anchor"], "label": row["label"],
            "original_solution_sha256": row["solution"]["sha256"],
            "replacement_html": replacement,
            "replacement_solution_sha256": digest(replacement.encode()),
            "decision": decision,
            "baseline_adequacy": "adequate" if decision == "retain" else "needs_expansion",
            "thoroughness_rationale": rationale,
            "specific_improvements": improvements,
            "questions_and_hints_preserved": True,
            "scope": "Only the exact editable solution body is proposed; original question, hint, outer disclosure and wrappers are retained.",
        })
    result = {
        "schema_version": 1, "status": "authored_probability_solution_drafts_pending_independent_review",
        "author": "/root/review_gaussian35",
        "page": "SafeLearning/primer-probability.html",
        "baseline": {"file": str(BASELINE.relative_to(ROOT)), "sha256": digest(BASELINE.read_bytes())},
        "page_contract": {"file": "page_contract.md", "sha256": digest((ROOT / "page_contract.md").read_bytes()), "read_fully": True},
        "audience": "First-course linear algebra and single-variable calculus.",
        "counts": {"exercises": 44, "replace": 42, "retain": 2},
        "exercises": drafts,
        "canonical_sources_owners_progress_publication_edited": False,
        "questions_hints_anchors_existing_disclosures_changed": False,
        "new_citations": [],
        "numeric_scope": "Preserve exact mathematical expressions and all Source90 qualifications about rounded quantiles, confidence intervals, model probability, dependence, atom splitting and conditional coverage.",
    }
    destination = OUT / "primer-probability-expanded-solutions-v1.json"
    with destination.open("x") as stream:
        json.dump(result, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "file": str(destination.relative_to(ROOT)),
                      "sha256": digest(destination.read_bytes()), "counts": result["counts"]}))


if __name__ == "__main__":
    main()
