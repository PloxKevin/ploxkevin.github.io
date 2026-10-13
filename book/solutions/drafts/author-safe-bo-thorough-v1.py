"""Prepare SafeOpt Source90 solution decisions; leave teaching sources untouched."""
from pathlib import Path
from hashlib import sha256
import json

BASE = Path('book/solutions/baseline-source90/pages/safe-bo.html.json')
DEST = Path('book/solutions/drafts/safe-bo-thorough-solutions-v1.json')
replacement = {}
rationale = {}


def replace(anchor, why, body):
    replacement[anchor] = body.strip() + '\n'
    rationale[anchor] = why


replace('exercise-16', 'Prove joint coverage and endpoint/candidate monotonicity, give all three rounds of a leave-and-return example, and show the exact sampled-width inequality that fails without nesting.', r'''
<p><strong>(a) One event covers every intersection.</strong> Work on the event $E$ supplied by the lemma: $f(x)\in Q_s(x)$ for every point $x$ and every round $s$. The seed is truly safe, so $f(x)\in C_0(x)$ too: $C_0(x)=[h,\infty)$ on the seed and $C_0(x)=\mathbb R$ elsewhere. For a fixed $x$ and $t$, its true value therefore belongs to every set being intersected, giving</p>
<div class="math-block">$$f(x)\in C_0(x)\cap\bigcap_{s=1}^t Q_s(x)=C_t(x).$$</div>
<p>This reasoning holds for every $x,t$ on the same event $E$. Thus the intersections are all nonempty there, and the probability remains at least $1-\delta$. The lemma already gives simultaneous coverage; this implication introduces no additional random event that needs another union bound.</p>
<p><strong>(b) Nested intervals and shrinking candidate sets.</strong> Write $Q_{t+1}(x)=[q^-_{t+1}(x),q^+_{t+1}(x)]$. Since $C_{t+1}=C_t\cap Q_{t+1}$, nonemptiness gives</p>
<div class="math-block">$$l_{t+1}(x)=\max\{l_t(x),q^-_{t+1}(x)\}\ge l_t(x),$$</div>
<div class="math-block">$$u_{t+1}(x)=\min\{u_t(x),q^+_{t+1}(x)\}\le u_t(x).$$</div>
<p>Subtracting yields $w_{t+1}(x)=u_{t+1}(x)-l_{t+1}(x)\le w_t(x)$. For a stage with $S_{t+1}=S_t=S$, the excluded points $D\setminus S$ are fixed. If an excluded $z$ satisfies $u_{t+1}(x)-Ld(x,z)\ge h$, it also satisfies $u_t(x)-Ld(x,z)\ge h$. Thus the expander count can only decrease, and $G_{t+1}\subseteq G_t$.</p>
<p>Similarly, put $b_t=\max_{z\in S}l_t(z)$. Pointwise growth of the lower bounds gives $b_{t+1}\ge b_t$. If $x\in M_{t+1}$, then</p>
<div class="math-block">$$u_t(x)\ge u_{t+1}(x)\ge b_{t+1}\ge b_t,$$</div>
<p>so $x\in M_t$. Combining the two inclusions gives $G_{t+1}\cup M_{t+1}\subseteq G_t\cup M_t$. The fixed-safe-set condition matters: new safe points can create new candidates when a stage changes.</p>
<p><strong>(c) A point can leave and return without intersection.</strong> Take the fixed safe set and whole domain $S=D=\{a,b\}$, with $h=0$, true values $f(a)=0.95$, $f(b)=0.5$, and the following valid raw intervals:</p>
<table><thead><tr><th>Round</th><th>$Q(a)$</th><th>$Q(b)$</th><th>Best lower bound</th><th>$M$</th></tr></thead><tbody><tr><td>$t-1$</td><td>$[0.7,1.2]$</td><td>$[0.2,0.8]$</td><td>$0.7$</td><td>$\{a,b\}$</td></tr><tr><td>$t$</td><td>$[0.9,1.2]$</td><td>$[0.2,0.8]$</td><td>$0.9$</td><td>$\{a\}$</td></tr><tr><td>$t+1$</td><td>$[0.75,1.0]$</td><td>$[0.2,0.8]$</td><td>$0.75$</td><td>$\{a,b\}$</td></tr></tbody></table>
<p>At $t-1$, $u(b)=0.8\ge0.7$; at $t$, $0.8\lt0.9$; at $t+1$, $0.8\ge0.75$. Thus $b$ leaves and re-enters, even though the raw width at $a$ decreases from $0.5$ to $0.3$ to $0.25$ and every interval contains the truth. A shrinking posterior variance does not make a moving lower endpoint monotone.</p>
<p>There are no expanders because no point lies outside $S$. At round $t$ the only eligible query is $a$, of width $0.3$. At $t+1$ the returned candidate $b$ has width $0.6$, exceeding $a$'s width $0.25$, so the acquisition selects $b$. The sampled width has increased from $0.3$ to $0.6$. With intersection, the interval at $a$ after these rounds is $[0.9,1.0]$, the best lower bound remains $0.9$, and $b$ cannot return.</p>
<p>The sample-complexity proof needs, inside a stage,</p>
<div class="math-block">$$w_{t+1}(x_{t+1})\le w_t(x_{t+1})\le w_t(x_t).$$</div>
<p>The first step uses pointwise nesting. The second uses $x_{t+1}\in G_t\cup M_t$ and the fact that $x_t$ maximizes width there. Re-entry invalidates that membership. Consequently the proof cannot bound the last sampled width by every earlier one to obtain $(t-t_0)w_t(x_t)^2\le\sum_{j=t_0+1}^t w_j(x_j)^2$. Safety alone still follows from valid current lower bounds and Lipschitz transfer; the missing property is the monotonicity needed for this finite-sample argument.</p>
''')

replace('exercise-17', 'Compute each epsilon-reachability iterate, prove the resulting set is a fixed point by checking every possible witness, and distinguish safe connectivity from Lipschitz certifiability and GP-only extrapolation.', r'''
<p><strong>(a) Verify the Lipschitz constant.</strong> The absolute adjacent differences, in order, are $0.7,0.8,0.6,1.0,0.2,0.9,1.0$, each at most $1$. For integers $i\lt j$, telescope and apply the triangle inequality:</p>
<div class="math-block">$$|f(j)-f(i)|\le\sum_{k=i}^{j-1}|f(k+1)-f(k)|\le j-i=|j-i|.$$</div>
<p>The same statement holds with the endpoints reversed, and equal endpoints give zero. Hence $f$ is $1$-Lipschitz on all of $D$.</p>
<p><strong>(b) Reachability with $\epsilon=0.2$.</strong> With $h=0$ and $L=1$, a witness $x\in S$ can add $z$ exactly when $f(x)-0.2-|x-z|\ge0$, or $|x-z|\le f(x)-0.2$. Existing points are kept by the $S$ term in $R_\epsilon(S)$.</p>
<p>The initial witness $2$ has radius $2.0-0.2=1.8$. Integer points at distance at most $1.8$ are $1,2,3$, so $R_\epsilon(S_0)=\{1,2,3\}$. The next update uses all three witnesses:</p>
<table><thead><tr><th>Witness $x$</th><th>Radius $f(x)-0.2$</th><th>Grid points certified</th></tr></thead><tbody><tr><td>$1$</td><td>$1.0$</td><td>$\{0,1,2\}$</td></tr><tr><td>$2$</td><td>$1.8$</td><td>$\{1,2,3\}$</td></tr><tr><td>$3$</td><td>$1.2$</td><td>$\{2,3,4\}$</td></tr></tbody></table>
<p>The union is $R_\epsilon^2(S_0)=\{0,1,2,3,4\}$. Newly available witnesses $0$ and $4$ have radii $0.3$ and $0.2$, so each certifies only itself. The other three witnesses have already been used. Therefore the third update adds nothing: this set is a fixed point and</p>
<div class="math-block">$$\bar R_{0.2}(S_0)=\{0,1,2,3,4\},\qquad f^*_{0.2}=\max\{0.5,1.2,2.0,1.4,0.4\}=2.0.$$</div>
<p>The reachable maximum is attained at $x=2$.</p>
<p><strong>(c) Reachability with no slack.</strong> Now the radius at the initial witness $2$ is exactly $2.0$, so even the first update includes the endpoints at distance $2$: $R_0(S_0)=\{0,1,2,3,4\}$. To check that no later update adds $5$, compute $f(x)-|x-5|$ for every possible witness in this set:</p>
<div class="math-block">$$(0.5-5,\ 1.2-4,\ 2.0-3,\ 1.4-2,\ 0.4-1)=(-4.5,-2.8,-1.0,-0.6,-0.6).$$</div>
<p>All are below $h=0$. Targets $6$ and $7$ are farther from each of these witnesses, so their transferred bounds are smaller still. There are no excluded points on the left. Thus $\bar R_0(S_0)=\{0,1,2,3,4\}$ as well.</p>
<p><strong>(d) Why a safe path is insufficient.</strong> Every true value is nonnegative, including the shallow valley at $4$ and $5$, but none of the reachable points has enough headroom to pay the Lipschitz distance to $5$. Even exact knowledge of $f$ would not make a witness-based certificate succeed there. SafeOpt's certified sets stay inside $\bar R_0(S_0)$ on the confidence event, so it cannot evaluate or recommend the global maximizer $7$, whose value is $2.1$.</p>
<p>The stated benchmark is instead $f^*_{0.2}=2.0$. A recommendation satisfying the $0.2$-optimality guarantee has value at least $1.8$; among the reachable points, only $2$ meets that requirement. This explains the scope of the guarantee without claiming that all safe points are explored.</p>
<p>The Lipschitz-free variant admits $5$ if its own valid GP lower bound clears the threshold, $\mu_t(5)-\beta_t\sigma_t(5)\ge0$. Kernel correlations can make that happen even though no Lipschitz witness reaches it, but the given values and $L$ alone do not determine the GP posterior or guarantee that it happens. If data confined to the left leave too much residual uncertainty at $5$, it remains uncertified. This variant therefore may pass the valley with additional valid kernel information; its safety and its ability to explore must be assessed under those additional assumptions.</p>
''')

replace('exercise-19', 'Show the normal difference and Bernoulli entropy, derive both conditional Gaussian means/variances and the predictive integrals, reproduce the expected entropies, and derive both fidelity choices from conditioning and effort.', r'''
<p><strong>(a) Optimistic minimization.</strong> For a cost, the lower-confidence-bound rule minimizes $\mu-2\sigma$. The scores are $1.0-2(0.6)=-0.2$ at $A$ and $1.2-2(0.1)=1.0$ at $B$. Since $-0.2\lt1.0$, it evaluates $\theta_A$.</p>
<p><strong>(b) Uncertainty about the minimizer.</strong> Independence makes the difference Gaussian, with mean $1.0-1.2=-0.2$ and variance $0.6^2+0.1^2=0.37$. Standardizing the event $J_A-J_B\lt0$ gives</p>
<div class="math-block">$$p_{\min}=\Pr(J_A\lt J_B)=\Phi\left(\frac{0.2}{\sqrt{0.37}}\right)\approx0.62885.$$</div>
<p>The minimizer is $A$ with this probability and $B$ with probability $1-p_{\min}\approx0.37115$. Ties have probability zero. Its binary entropy is</p>
<div class="math-block">$$H=h_b(p_{\min}),\qquad h_b(p)=-p\ln p-(1-p)\ln(1-p),$$</div>
<p>giving $H\approx0.65957$ nats. Natural logarithms fix the unit.</p>
<p><strong>(c) Expected entropy after a measurement.</strong> For a scalar prior $J\sim\mathcal N(m,v)$ and observation $Y=J+\varepsilon$ with independent noise variance $r$, Gaussian conditioning gives</p>
<div class="math-block">$$m^+(y)=m+\frac{v}{v+r}(y-m),\qquad v^+=v-\frac{v^2}{v+r}=\frac{vr}{v+r}.$$</div>
<p>The value $y$ is unknown when choosing the experiment, so the entropy after the update must be averaged over $Y\sim\mathcal N(m,v+r)$.</p>
<p>At $A$, use $v=0.36$ and $r=0.01$. Then $v_A^+=0.0036/0.37\approx0.00972973$ and $\sigma_A^+=\sqrt{v_A^+}\approx0.09864$. Write the predictive observation as $Y_A=1+\sqrt{0.37}Z$, with $Z\sim\mathcal N(0,1)$. The updated mean is</p>
<div class="math-block">$$m_A(Z)=1+\frac{0.36}{\sqrt{0.37}}Z.$$</div>
<p>Before observation this mean has standard deviation $0.36/\sqrt{0.37}\approx0.59184$. The belief at $B$ is unchanged, because the candidates and their observation noises are independent. Conditional on $Z$, the difference $J_A-J_B$ has mean $m_A(Z)-1.2$ and variance $v_A^++0.01\approx0.01972973$. Therefore</p>
<div class="math-block">$$p_A(Z)=\Phi\left(\frac{1.2-m_A(Z)}{\sqrt{v_A^++0.01}}\right),$$</div>
<div class="math-block">$$\mathbb E[H_A^+]=\int_{-\infty}^{\infty}h_b(p_A(z))\,\phi(z)\,dz\approx0.15738\ \text{nats}.$$</div>
<p>Here $\phi(z)=e^{-z^2/2}/\sqrt{2\pi}$ and the continuous endpoint convention is $h_b(0)=h_b(1)=0$. Numerical quadrature of this one-dimensional integral gives the displayed value. For example, Simpson's rule on $[-8,8]$ with step $0.001$ suffices at the displayed precision; the omitted tails contribute at most $\ln2\,\Pr(|Z|\gt8)$. The expected reduction is approximately $0.65957-0.15738=0.50219$ nats. The updated mean moves on a scale $0.59$, much larger than the residual difference standard deviation $\sqrt{0.01972973}\approx0.14046$, so it usually makes the ordering quite clear.</p>
<p>At $B$, $v=r=0.01$, so $v_B^+=0.005$ and $\sigma_B^+=\sqrt{0.005}\approx0.07071$. Now $Y_B=1.2+\sqrt{0.02}Z$ and the conditioning gain is $1/2$, giving $m_B(Z)=1.2+\sqrt{0.005}Z$. The variance at $A$ remains $0.36$. Thus</p>
<div class="math-block">$$p_B(Z)=\Pr(J_A\lt J_B\mid Y_B)=\Phi\left(\frac{0.2+\sqrt{0.005}Z}{\sqrt{0.365}}\right),$$</div>
<div class="math-block">$$\mathbb E[H_B^+]=\int_{-\infty}^{\infty}h_b(p_B(z))\,\phi(z)\,dz\approx0.65541\ \text{nats}.$$</div>
<p>The reduction is only about $0.00415$ nats: the new mean at $B$ moves on a scale $0.071$, while the large uncertainty at $A$ remains. Entropy Search therefore chooses $A$ here, agreeing with the LCB choice for this particular independent pair. This calculation compares information about the minimizer; it does not supply a separate safety certificate for either experiment.</p>
<p><strong>(d) Information per unit effort.</strong> Interpret the simulation as noise-free, as in Section 5.2. Initially $J(\theta,1)=J_{\rm sim}(\theta)+J_{\rm err}(\theta)$ has variance $0.8+0.2=1$, and its covariance with the simulated value is $0.8$. Conditioning on that value leaves variance</p>
<div class="math-block">$$v_{m sim}^+=1-\frac{0.8^2}{0.8}=0.2.$$</div>
<p>A robot observation has variance $1+0.05=1.05$ and covariance $1$ with the true robot cost, so it leaves</p>
<div class="math-block">$$v_{m exp}^+=1-\frac{1^2}{1.05}=\frac1{21}\approx0.047619.$$</div>
<p>The proxy information gains are $I_{\rm sim}=\tfrac12\ln(1/0.2)=\tfrac12\ln5\approx0.804719$ and $I_{\rm exp}=\tfrac12\ln21\approx1.522261$ nats. These are prior-to-one-observation comparisons; neither variance depends on the returned measurement.</p>
<table><thead><tr><th>Simulation effort</th><th>$I_{\rm sim}/t_{\rm sim}$</th><th>$I_{\rm exp}/1$</th><th>Choice</th></tr></thead><tbody><tr><td>$0.6$</td><td>$1.341198$</td><td>$1.522261$</td><td>robot experiment</td></tr><tr><td>$0.25$</td><td>$3.218876$</td><td>$1.522261$</td><td>simulation</td></tr></tbody></table>
<p>A simulator leaves the independent model-error variance untouched at this initial step, but it can still win when its effort is sufficiently low. The actual multi-fidelity Entropy Search acquisition measures information about the location of the real-system minimum; the question's scalar-variance proxy makes the cost-versus-information calculation explicit.</p>
''')

retained = {
    'book-m4-b1': 'Both transferred margins are computed in their own units, the failing constraint is identified, each radius is divided by its Lipschitz constant, and the simultaneous admissible radius is their minimum. This completes the two requested decisions without further steps.',
    'book-m4-b2': 'Uses the worst realized distance d+0.04, intersects the two radii, solves d<=0.26, and exhibits the vibration failure for 0.28 at an allowed realization. The text explains why the nominal margin does not cover all implemented gains.',
    'practice-1': 'Computes the noisy value, compares the true value to the threshold, and gives an explicit unsafe underlying value producing a positive observation. It distinguishes prior permission from retrospective measurement, covering every conceptual subpart.',
    'practice-2': 'Solves the Lipschitz inequality, evaluates all three distances including the inclusive boundary, and states metric and bound validity. The short arithmetic is complete.',
    'practice-3': 'Computes the maximum of all lower bounds, compares each upper bound to it, identifies the exact candidate set and lower-bound recommendation, and distinguishes the recommendation from a measurement.',
    'practice-4': 'Forms the eligible union, compares its three widths, excludes the uncertified point, and explains the order of safety permission and information scoring.',
    'practice-5': 'Uses maximum lower/minimum upper endpoints, computes the nonempty intersection and width, then diagnoses the disjoint case without treating emptiness as a certificate. It explains why simultaneous truth coverage makes emptiness impossible on the event.',
    'practice-6': 'Computes both optimistic transfers to the sole excluded point, the maximizer threshold, both widths and the selected query. It also computes the negative current lower transfer to prevent interpreting potential expansion as actual certification.',
    'practice-7': 'Checks every constraint at every parameter including equality, gives the exact intersection set, and explains why an objective upper bound cannot replace the missing constraint evidence.',
    'practice-8': 'Shows each successive reachability set and the witness for each new point, checks all three transfers to the remaining excluded point, and identifies the fixed point and true-safe but unreachable parameter.',
    'practice-9': 'States the safe seed base and the membership witness, chains Lipschitz continuity, simultaneous lower validity and the certification inequality, then explains the role of the event and query restriction. Each assumption has an explicit use.',
    'practice-10': 'Lists each per-query regret, computes sum, average and simple regret, and proves their different scopes with repeated costly queries leaving the final recommendation unchanged.',
    'practice-11': 'Applies each valid endpoint to the comparison maximum and the recommended value, subtracts to obtain 0.08, and explicitly limits the result to the certified comparison set.',
    'practice-12': 'Chooses a covering grid point for an arbitrary decision, applies the Lipschitz decrement to obtain uniform margin 0.02, and recomputes the weaker -0.10 bound for merely nonnegative grid values.',
    'exercise-15': 'All three proof parts are present: seed-based safety induction with the entire inequality chain, reachability induction with monotonicity and fixed-point closure, and the exact use of seed truth in the initial interval and self-certification. No hidden additional union bound is used.',
    'exercise-18': 'Proves the first-crossing contradiction using an intervening unsafe grid point, identifies the recommendation and benchmark restriction, and explains trajectory backups. Its optional kernel examples are already supported by the rank-one structure and explicit squared-exponential RKHS feature expansion, norm computation and deterministic residual bound; the numerical certificate has been independently checked.',
}

if __name__ == '__main__':
    baseline = json.loads(BASE.read_bytes())
    decisions = []
    for exercise in baseline['exercises']:
        anchor = exercise['anchor'] or exercise['inventory_key'].split('::')[-1]
        body = replacement.get(anchor, exercise['solution']['html'])
        why = rationale.get(anchor, retained.get(anchor))
        assert why, 'Missing assessment: ' + anchor
        decisions.append({
            'inventory_key': exercise['inventory_key'],
            'source_file': exercise['source_file'],
            'authoring_file': exercise['authoring_file'],
            'ordinal': exercise['ordinal'],
            'label': exercise['label'],
            'original_solution_sha256': exercise['solution']['sha256'],
            'decision': 'replace' if anchor in replacement else 'retain',
            'thoroughness_rationale': why,
            'replacement_html': body,
            'selected_solution_sha256': sha256(body.encode()).hexdigest(),
        })
    assert len(decisions) == 19 and len(replacement) + len(retained) == 19
    result = {
        'schema_version': 1,
        'status': 'author_draft_requires_independent_math_depth_and_render_review',
        'author': 'solution_review_rotation',
        'page': 'SafeLearning/safe-bo.html',
        'baseline': {'file': str(BASE), 'sha256': sha256(BASE.read_bytes()).hexdigest()},
        'audience': 'First-course linear algebra and single-variable calculus.',
        'page_contract': {'file': 'page_contract.md', 'sha256': sha256(Path('page_contract.md').read_bytes()).hexdigest(), 'read_fully': True},
        'counts': {'exercises': 19, 'retain': len(retained), 'replace': len(replacement)},
        'exercises': decisions,
        'canonical_sources_or_coverage_records_edited': False,
        'new_citations': [],
    }
    with DEST.open('x', encoding='utf-8') as handle:
        json.dump(result, handle, indent=2, ensure_ascii=False)
        handle.write('\n')
    print(json.dumps({'file': str(DEST), 'sha256': sha256(DEST.read_bytes()).hexdigest(), 'counts': result['counts']}))
