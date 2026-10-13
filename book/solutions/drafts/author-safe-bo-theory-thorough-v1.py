"""Prepare complete LoSBO/Real-beta solution decisions from immutable Source90."""
from pathlib import Path
from hashlib import sha256
import json

BASE = Path('book/solutions/baseline-source90/pages/safe-bo-theory.html.json')
DEST = Path('book/solutions/drafts/safe-bo-theory-thorough-solutions-v1.json')
baseline = json.loads(BASE.read_bytes())
original = {e['anchor'] or e['inventory_key'].split('::')[-1]: e['solution']['html'] for e in baseline['exercises']}
replacement = {}
rationale = {}

def replace(anchor, why, body):
    replacement[anchor] = body.strip() + '\n'
    rationale[anchor] = why

replace('book-m5-b2', 'Derive the finite-run envelope by conditional tails, averaging and union bound; solve the logarithmic inequality and then the first cone radius, stating the finite-horizon probability.', r'''
<p>Let $\mathcal F_{i-1}$ denote the information used to choose experiment $i$. The conditional Gaussian assumption gives the same tail estimate after every possible history:</p>
<div class="math-block">$$\Pr(|\epsilon_i|\gt E\mid\mathcal F_{i-1})\le2\exp\left(-\frac{E^2}{2(0.15)^2}\right).$$</div>
<p>Averaging this inequality over the history gives the same unconditional bound. Thus adaptation of the gains does not invalidate it. The union bound for at most 100 experiments gives</p>
<div class="math-block">$$\Pr\big(\exists i\le100:|\epsilon_i|\gt E\big)\le200\exp\left(-\frac{E^2}{2(0.15)^2}\right).$$</div>
<p>Independence between these events is unnecessary. To make the right side at most $0.01$, require</p>
<div class="math-block">$$\exp\left(-\frac{E^2}{2(0.15)^2}\right)\le\frac{0.01}{200}.$$</div>
<p>Take logarithms, multiply by $-1$ with the inequality reversed, and take the nonnegative square root. A sufficient choice is</p>
<div class="math-block">$$E=0.15\sqrt{2\ln(200/0.01)}\approx0.667575\ \text{degrees}.$$</div>
<p>On the event that every error stays in this envelope, the first reading implies $f(0)\ge0.95-E$. With the lab's $L=0.8$ and threshold $h=0$, the cone is nonnegative precisely when</p>
<div class="math-block">$$|a|\le\frac{0.95-E}{0.8}\approx0.353031.$$</div>
<p>The first certified interval is therefore the closed interval with that radius about zero, in the lab's full real-line domain. The nonnegative numerator is essential; a negative one would certify no new point. On the same event the usual deterministic induction applies to all queries made using this common envelope, so the probability of a safe run of at most 100 experiments is at least $0.99$, assuming the seed and Lipschitz bound remain valid.</p>
<p>This radius is smaller than the original radius $(0.95-0.15)/0.8=1$ because the new bound covers Gaussian tails over the planned run. It is a finite-horizon probabilistic statement. Continuing beyond 100 requires an additional budget or a bound constructed for all times.</p>
''')

replace('exercise-18', 'Track the page’s two indexing conventions, compute all three cones and unions, identify both initially excluded planned gains, and give a compatible explicit true function proving the danger of an underestimated L.', r'''
<p><strong>(a) Single-constraint LoSBO.</strong> Use Algorithm 3's indexing: $S_t$ is available <em>before</em> query $t$, so $S_1=S_0=\{0.5\}$. A measurement $(z,y)$ adds grid points satisfying $|x-z|\le(y-E-h)/L$.</p>
<p>After the first reading, the radius is $(1.4-0.2)/3=0.4$. Its continuous interval is $[0.1,0.9]$, and intersecting it with the grid gives</p>
<div class="math-block">$$S_2=\{0.1,0.2,\ldots,0.9\}.$$</div>
<p>The planned next query $0.9$ is included, even at the endpoint. Its reading $0.8$ gives radius $(0.8-0.2)/3=0.2$. The resulting interval $[0.7,1.1]$ is clipped to $D$, adding $1.0$ to the previous set. Hence</p>
<div class="math-block">$$S_3=\{0.1,0.2,\ldots,1.0\}.$$</div>
<p>The third query $0.1$ is in this set. Its reading $0.25$ gives radius $(0.25-0.2)/3=1/60\approx0.016667$. The interval $[0.1-1/60,0.1+1/60]$ contains only the grid point $0.1$, already certified, so $S_4=S_3$. This last update explains the role of the third measurement, although the requested sets stop at $S_3$. Stored certificates are united; the small new cone does not remove earlier points.</p>
<p><strong>(b) Add constraint 2.</strong> Its first reading at $0.5$ gives radius $(0.35-0.1)/1=0.25$. The continuous interval $[0.25,0.75]$ contains the grid points $\{0.3,0.4,0.5,0.6,0.7\}$. Constraint 1 certifies $\{0.1,\ldots,0.9\}$. Their intersection is</p>
<div class="math-block">$$S_1^{\rm MC}=\{0.3,0.4,0.5,0.6,0.7\}.$$</div>
<p>Section 5's MCLoSBO convention calls the seed measurement round zero, so its set <em>after</em> that measurement is $S_1^{\rm MC}$; it corresponds to the timing of $S_2$ in part (a). The planned query $0.9$ is now inadmissible and is the first point where the proposed sequence must change. The other planned gain $0.1$ is also outside this initial joint set. Later valid measurements could enlarge it, but the supplied data do not yet permit either gain. The next experiment must lie in $S_1^{\rm MC}$ and measure both constraints; the GP may rank such permitted experiments.</p>
<p><strong>(c) An invalid slope bound can admit unsafe inputs.</strong> With the incorrectly used $L=2$, the first radius is $(1.4-0.2)/2=0.6$. Its interval $[-0.1,1.1]$ contains the entire grid, so the algorithm claims $S_2=D$, including $0$. But the stipulated true value is $f(0)=-0.1\lt h$.</p>
<p>For a concrete consistency check, use the following continuous piecewise-linear function on $[0,1]$, restricted to the grid:</p>
<div class="math-block">$$f(x)=\begin{cases}-0.1+1.5x,&0\le x\le0.1,\\0.05+2.875(x-0.1),&0.1\le x\le0.5,\\1.2-1.5(x-0.5),&0.5\le x\le0.9,\\0.6,&0.9\le x\le1.\end{cases}$$</div>
<p>Adjacent pieces join at values $0.05$, $1.2$, and $0.6$. Every slope has magnitude at most $2.875\le3$, so the original $L=3$ is valid; summing losses across the pieces proves the same bound for endpoints in different pieces. The three observations are compatible with allowed error $+0.2$ at their respective centers: $1.2+0.2=1.4$, $0.6+0.2=0.8$, and $0.05+0.2=0.25$. The seed is safe, while $f(0)=-0.1$ is unsafe. The function also has slope $2.875\gt2$, so the substituted bound is invalid.</p>
<p>Certification of $0$ does not force its selection, but it allows an acquisition rule to select it and thereby violate safety. Underestimating $L$ can therefore break the gate even when the original Lipschitz/noise assumptions and the seed are correct.</p>
''')

# Preserve the already complete probability and shell analysis in (a)-(b),
# while adding the algebra for the finite-horizon envelope and false-alarm margin.
prefix = original['exercise-19'].split('<p><em>(c)</em>')[0]
replace('exercise-19', 'Keep the worked Gaussian exceedance and one-sided shell argument, derive the horizon envelope rather than only state it, and prove exactly what doubling the hard bound does, including the seed margin condition.', prefix + r'''
<p><strong>(c) A finite-horizon replacement.</strong> For $E_T\ge0$, the Gaussian tail estimate and union bound give</p>
<div class="math-block">$$\Pr\big(\exists t\le T:|\epsilon_t|\gt E_T\big)\le2T\exp\left(-\frac{E_T^2}{2\sigma_n^2}\right).$$</div>
<p>Make this at most $\delta$ by requiring $\exp[-E_T^2/(2\sigma_n^2)]\le\delta/(2T)$. Taking logarithms and reversing the inequality after multiplication by $-1$ gives $E_T^2\ge2\sigma_n^2\ln(2T/\delta)$. Therefore</p>
<div class="math-block">$$E_T=\sigma_n\sqrt{2\ln(2T/\delta)}$$</div>
<p>is sufficient. For $T=25$ and $\delta=0.01$, $2T/\delta=5000$, so $E_T/\sigma_n=\sqrt{2\ln5000}\approx4.12727$. Independence is unnecessary for this union-bound construction, although it was used for the exact probability in (a).</p>
<p>On the event that all planned errors satisfy this bound, the LoSBO cone inequalities and induction hold for every query made with $E=E_T$. With a valid Lipschitz bound, stationary function and safe seed, this gives safety with probability at least $1-\delta$ over the planned $T$ experiments. It supplies no deterministic all-time statement about Gaussian noise. An anytime construction must allocate a summable tail budget across rounds.</p>
<p><strong>(d) Doubling a genuine hard bound prevents misleading low readings.</strong> The paper assumes actual bounded noise $|\epsilon_s|\le B_\epsilon$, and chooses the more conservative cone allowance $E=2B_\epsilon$. If a measurement at $z$ certifies $x$, then $y_s-2B_\epsilon-Ld(z,x)\ge h$. The actual bound and Lipschitz continuity give</p>
<div class="math-block">$$f(x)\ge y_s-B_\epsilon-Ld(z,x)\ge h+B_\epsilon.$$</div>
<p>A later measurement at this point consequently satisfies $y=f(x)+\epsilon\ge h+B_\epsilon-B_\epsilon=h$. Thus an actually safe experiment cannot produce an apparent below-threshold reading there. Seed points, which were supplied independently rather than added by a cone, also need the margin $f\ge h+B_\epsilon$ for this measurement guarantee.</p>
<p>With the smaller cone allowance $E=B_\epsilon$, true-value safety still holds, but a point near $f=h$ may return $y\lt h$ under negative noise and trigger an unnecessary stop. Doubling the bound trades a smaller admitted region for a margin against that false alarm. It addresses bounded measurement error; Gaussian unboundedness instead needs a construction such as part (c).</p>
''')

replace('exercise-20', 'Show each logarithm, prefactor and numerical multiplier, distinguish the prescribed realized-gain substitutions from applicable theorem bounds, and interpret the heuristic relative to a norm upper bound without asserting the true norm equals it.', r'''
<p>All logarithms are natural. The supplied design has realized information gain $G_{20}=\tfrac12\ln\det(I+K/\lambda)=12/2=6$. Use this number for the substitutions requested in the question.</p>
<p><strong>Data-dependent eq. (7).</strong> The regularization prefactor is $R/\sqrt\lambda=0.05/\sqrt{0.05}=\sqrt{0.05}\approx0.2236068$, and $2\ln(1/\delta)=2\ln100\approx9.2103404$. Hence</p>
<div class="math-block">$$\begin{aligned}\beta_{20}&=10+\sqrt{0.05}\sqrt{12+2\ln100}\\&=10+\sqrt{0.05}\sqrt{21.2103404}\approx11.0298141.\end{aligned}$$</div>
<p>Eq. (7) uses the actual design and permits the supplied $\lambda=0.05$. Its confidence conclusion still requires the correct kernel, norm upper bound and conditional sub-Gaussian noise assumptions.</p>
<p><strong>Chowdhury&ndash;Gopalan numerical substitution.</strong> Replacing its information-gain term by $6$ gives</p>
<div class="math-block">$$10+0.05\sqrt{2(6+1+\ln100)}\approx10.2408856.$$</div>
<p>This is an illustrative value, not a valid alternative confidence radius for the same posterior: the cited theorem prescribes $\lambda=1+2/T\ge1$, rather than $0.05$, and its information gain is a maximum over designs at its specified index. The supplied $G_{20}$ is one realized design after 20 observations, not that maximum after $t-1$ observations. A realized gain may underestimate the maximum; the question's substitution alone cannot establish the theorem's guarantee.</p>
<p><strong>Srinivas-type numerical substitution.</strong> Here $t/\delta=20/0.01=2000$, $\ln2000\approx7.6009025$, and its cube is approximately $439.1037$. Thus</p>
<div class="math-block">$$\sqrt{2(10)^2+300(6)(\ln2000)^3}\approx889.1784.$$</div>
<p>This curve likewise uses the requested realized-gain proxy. The cited Srinivas theorem uses maximal information gain and its own bounded-noise and regularization assumptions; the numerical comparison does not transfer that guarantee to a different setting.</p>
<p><strong>Compare with the heuristic $2$.</strong> The two modern expressions are dominated by the norm upper bound $B=10$: their added terms are about $1.03$ and $0.241$. For the data-dependent eq. (7), the halfwidth at the same posterior standard deviation is $11.0298/2\approx5.515$ times the heuristic halfwidth. To justify multiplier $2$ through eq. (7) for this design and noise/regularization choice would require a valid $B$ satisfying $B+1.0298141\le2$, or $B\le0.9701859$.</p>
<p>The supplied upper bound $B=10$ does not imply that the actual norm equals 10; it does mean that this available assumption cannot justify $2$ through the displayed theorem. The very large Srinivas-type value explains its conservatism. A valid radius can preserve safety while slowing expansion, because lower endpoints may remain too small to certify new experiments. None of these numerical widths alone proves that the safe region will expand.</p>
''')

retained = {
 'book-m5-b1': 'Requires both endpoint containments, solves the exact contracted command interval, and gives the allowed realization that rejects 1.5. Boundary inclusion and strict-margin interpretation are explicit.',
 'practice-1': 'Computes slack and radius, clips the ball to the domain, evaluates both requested candidates and explains why previous certificates are retained.',
 'practice-2': 'Ranks only the two admitted candidates, excludes the attractive uncertified point, and identifies all physical assumptions that let the safety proof survive GP inaccuracy.',
 'practice-3': 'Computes both proposed radii and the tight valid radius at the true constant, separates valid conservative overestimation from invalid underestimation, and states the required global scope.',
 'practice-4': 'Computes the intersection and checks each listed parameter; explains unions within one constraint and intersections across all constraints through the witness quantifiers.',
 'practice-5': 'Shows both radii and intervals, the overlapping union and the seed addition. Explains negative slack and why stored stationary certificates remain valid.',
 'practice-6': 'Provides the explicit triangular function family, its two slopes and exact smallest Lipschitz constant. Endpoints match, and arbitrarily large slope shows the failure of inferring a global upper bound from one secant.',
 'practice-7': 'Substitutes the unit noise/regularization prefactor, computes the real multiplier and lower endpoint, compares the threshold, and distinguishes the heuristic numerical decision from a theorem-backed one.',
 'practice-8': 'Transfers across space at the observation time and then subtracts temporal drift, evaluates every term and explains the separate drift assumption needed beyond stationary LoSBO.',
 'practice-9': 'Constructs the downward cone and compatible maximal positive noise, proves its Lipschitz bound with the reverse triangle inequality, and derives unsafe values outside the radius. The scope is correctly limited to one observation.',
 'practice-10': 'Evaluates the inner and outer extrema in both orders, gives acceptance and rejection, and identifies the distinct valid witnesses for the two constraints.',
 'practice-11': 'Uses reproduction to prove the unobserved direction vanishes at every data point, uses orthogonality and Pythagoras for the exact squared norm, and states why existence of that direction is essential.',
 'practice-12': 'Computes the Gaussian interval probability, multiplies by independence, takes the zero infinite-horizon limit, and distinguishes failure of the hard-bound assumption from an inevitable physical violation.',
 'exercise-15': 'Proposes the correct asymmetric point/time-dependent rule, gives both base cases and the exact new-point chain, identifies the upper noise side and explains why negative noise is conservative. Query membership makes the result independent of beta.',
 'exercise-16': 'The RKHS construction includes residual projection, zero values at observations, the power-function identity, choice of coefficient and exact norm. The three-point example proves positive definiteness, valid L and seed, wrong lower bound, set admission and actual acquisition of the unsafe point; all intermediate bands and widths are shown.',
 'exercise-17': 'States the Holder update and inequality chain, explicitly rejects negative slack before inversion, computes both radii, solves the radius comparison on nonnegative slack, and explains the distance-unit dependence.',
}

if __name__ == '__main__':
    decisions=[]
    for e in baseline['exercises']:
        a=e['anchor'] or e['inventory_key'].split('::')[-1]
        body=replacement.get(a,e['solution']['html']);why=rationale.get(a,retained.get(a));assert why,a
        decisions.append({'inventory_key':e['inventory_key'],'source_file':e['source_file'],'authoring_file':e['authoring_file'],'ordinal':e['ordinal'],'label':e['label'],'original_solution_sha256':e['solution']['sha256'],'decision':'replace' if a in replacement else 'retain','thoroughness_rationale':why,'replacement_html':body,'selected_solution_sha256':sha256(body.encode()).hexdigest()})
    assert len(decisions)==20 and len(retained)+len(replacement)==20
    result={'schema_version':1,'status':'author_draft_requires_independent_math_depth_and_render_review','author':'solution_review_rotation','page':'SafeLearning/safe-bo-theory.html','baseline':{'file':str(BASE),'sha256':sha256(BASE.read_bytes()).hexdigest()},'audience':'First-course linear algebra and single-variable calculus.','page_contract':{'file':'page_contract.md','sha256':sha256(Path('page_contract.md').read_bytes()).hexdigest(),'read_fully':True},'counts':{'exercises':20,'retain':len(retained),'replace':len(replacement)},'exercises':decisions,'canonical_sources_or_coverage_records_edited':False,'new_citations':[]}
    with DEST.open('x',encoding='utf-8') as f:json.dump(result,f,indent=2,ensure_ascii=False);f.write('\n')
    print(json.dumps({'file':str(DEST),'sha256':sha256(DEST.read_bytes()).hexdigest(),'counts':result['counts']}))
