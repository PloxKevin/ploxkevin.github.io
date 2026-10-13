"""Prepare every viability solution decision against the immutable baseline."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
p=ROOT/'book/solutions/baseline-source90/pages/viability.html.json'
baseline=json.loads(p.read_bytes());replacements={};reasons={}
def add(key,reason,body):replacements[key]=body.strip()+'\n';reasons[key]=reason
add('book-m7-b1','Lists every elimination set and exhibits preserving actions for every surviving state, making the fixed-point and practical conclusion explicit.',r'''
<p><strong>1. Start with all states satisfying the relaxed cap.</strong> The candidate set is $K_0=\{52,54,56,58,60,62\}$ degrees. A pruning round keeps a state only if an available action has a successor in the current candidate set. At $62$, cooling is forbidden by the unchanged interlock and running gives $64$, outside $K_0$. Thus the first round removes $62$ and gives $K_1=\{52,54,56,58,60\}$.</p>
<p><strong>2. Propagate the loss of continuation backward.</strong> State $60$ survived the first round because running to $62$ was still in $K_0$. But now its only available successor, $62$, is outside $K_1$. The second round removes $60$, leaving $K_2=\{52,54,56,58\}$.</p>
<p><strong>3. Verify the fixed point state by state.</strong> Running sends $52$ to $54$ and $54$ to $56$. At $56$, running reaches $58$ and cooling reaches $52$. At $58$, cooling reaches $54$. Each surviving state therefore has at least one successor in $K_2$, so $K_3=K_2$. Following these choices gives an indefinitely safe continuation, and the removed states have none. Hence the viability kernel is exactly $\{52,54,56,58\}$, unchanged from the original cap.</p>
<p>The relaxed instantaneous limit allows a doomed trajectory one more step, but it supplies no sustainable action at high temperatures. Changing the cooling interlock or capacity would change the transition model; raising the temperature cap alone does not solve that controllability obstruction.</p>
''')
add('book-m7-b2','Derives the safe cycle value and exact strict threshold, checks the penalty and ties, and compares delayed rush departures with the safe continuation.',r'''
<p><strong>1. Recompute the continuing safe alternative.</strong> Starting at $58$, the best safe cycle is cooling to $54$ with reward $0$, running to $56$ with reward $3$, and running back to $58$ with reward $3$. At $\gamma=0.8$, its value solves $V_s=0+0.8(3)+0.8^2(3)+0.8^3V_s$. Rearranging gives</p>
<div class="math-block">$$V_s=\frac{2.4+1.92}{1-0.512}=\frac{4.32}{0.488}=\frac{540}{61}\approx8.852459.$$</div>
<p>The cooling detour at $56$ inserts extra steps before returning to the same productive cycle and is worse at these positive discounted rewards; the safe optimum therefore uses the stated cycle.</p>
<p><strong>2. Compare the complete unsafe route.</strong> Running at $58$ earns the rush reward $25$ and reaches $60$. Cooling is unavailable there, so the next run earns $3$ and incurs penalty $p$ before the absorbing failure state. Its return is $U_p=25+0.8(3-p)=27.4-0.8p$. To exclude every unsafe tie require $U_p\lt V_s$:</p>
<div class="math-block">$$p\gt\frac{27.4-540/61}{0.8}=\frac{5657}{244}\approx23.184426.$$</div>
<p>If departure is delayed by $n$ complete safe cycles, its return is $V_s+\gamma^{3n}(U_p-V_s)$. This follows by summing the rewards of those cycles and adding the discounted departure return. Thus when $U_p\lt V_s$, delaying an unsafe departure cannot improve on staying safe; when $U_p=V_s$, the immediate unsafe departure already ties.</p>
<p><strong>3. Test the requested penalty.</strong> For $p=24$, $U_p=27.4-0.8(24)=8.2\lt540/61$. The optimal action at $58$ is therefore cooling. At the exact threshold both cooling with safe continuation and the unsafe rush route maximize return, so the assertion that every maximizing action is safe fails. The strict inequality is essential. Relative to the original $0.9$ discount, the shorter reward horizon reduces the influence of delayed failure and raises the required penalty.</p>
''')
add('practice-6','Derives the safe geometric value, strict action comparison and exact return for delayed failure, covering both threshold sides and the tie.',r'''
<p><strong>1. Evaluate the indefinitely safe policy.</strong> Always staying earns reward $1$ every step, so its return is $S=1+\gamma+\gamma^2+\cdots=1/(1-\gamma)=2$ for $\gamma=1/2$. The geometric sum converges because $0\lt\gamma\lt1$.</p>
<p><strong>2. Evaluate a jump at any time.</strong> An immediate jump earns $4$ now and reaches failure value $-p$ one step later, giving $J=4-\gamma p=4-p/2$. If the controller first stays for $n$ steps and then jumps, its return is</p>
<div class="math-block">$$\sum_{t=0}^{n-1}\gamma^t+\gamma^nJ=\frac{1-\gamma^n}{1-\gamma}+\gamma^nJ=2+\gamma^n(J-2).$$</div>
<p>This compares all deterministic finite jump times as well as the safe alternative. For $p\gt4$, $J\lt2$, so every finite jump has return below $2$ and staying is the only optimal action at $A$. A randomized policy with positive probability of a finite jump also loses value, since each such outcome has a positive deficit.</p>
<p>At $p=4$, $J=2$ and jumping ties with staying, so not every optimal action is safe. For $p\lt4$, $J\gt2$ and $\gamma^n$ decreases with $n$; the immediate jump is better than every delayed one and better than staying. Hence the exact strict sufficient range is $p\gt4$.</p>
''')
add('practice-12','Introduces first-failure events and derives their probabilities from the history-conditional action bounds, making the independence-free episode guarantee explicit.',r'''
<p><strong>1. Add action risks within one decision.</strong> Conditional on any history that has kept the state viable, at most three critical actions each have probability at most $0.002$. These are different action choices, so their total probability is at most $3(0.002)=0.006$.</p>
<p><strong>2. Keep the history condition when moving to the episode.</strong> Let $S_{t-1}$ be the event that no critical action has occurred before decision $t$, and let $E_t$ be the event that the first critical action occurs at $t$. Starting in the viability kernel, on $S_{t-1}$ the relevant state remains viable. Conditioning on its possible histories and using the per-decision bound gives $\Pr(E_t)\le0.006\Pr(S_{t-1})\le0.006$.</p>
<p><strong>3. Sum the possible first times.</strong> The first-critical events $E_1,\ldots,E_{50}$ are disjoint, and their union is the event that some critical action is selected in the first $50$ decisions. Therefore its probability is at most $\sum_{t=1}^{50}\Pr(E_t)\le50(0.006)=0.3$. The probability of avoiding critical actions throughout is consequently at least $1-0.3=0.7$.</p>
<p>No independence is required. The premise must hold conditional on every relevant safe history, not merely as an unconditional probability measured at one state. The per-action bound, the total per-decision bound and the full-episode bound answer different questions.</p>
''')
retained={
'practice-1':'Identifies the safe self-loop, proves why the nonfailed intermediate state is doomed and checks both actions against the actual kernel.',
'practice-2':'Counts distinct viable actions including repeated successors, computes the fraction and explains why doomed nonfailed states are excluded.',
'practice-3':'Substitutes the failure arrival time in the discounted penalty and contrasts immediate failure, with the exact timing assumption stated.',
'practice-4':'Solves the strict inequality and all three parameter cases, distinguishing the threshold infimum from sufficient penalties and safe tie-breaking.',
'practice-5':'Lists every pruning set, explains the reason for each removed state and proves why the fixed-point self-loops yield indefinite safety.',
'practice-7':'Computes both uniform entropies and critical mass, states positive softmax temperature and proves finite scores cannot assign zero probability.',
'practice-8':'Proves both sufficiency and necessity of the interval maximum bound, evaluates both examples and states the tube-containment premise.',
'practice-9':'Compares each controller pointwise before taking suprema and uses inclusion of safe controllers to establish the second bound.',
'practice-10':'Computes all reward and penalty contributions and identifies exactly which nonnegative added terms justify extending the horizon.',
'practice-11':'Displays the fixed-point triangle/contraction inequality, rearrangement and numerical denominator, then explains why value error alone does not ensure policy safety.',
'::exercise-15':'Provides the braking trajectory, strict/closed boundary classification, explicit failure-time root and unbounded-time sequence, and distinct hold-input limits with their necessary-rate derivation.',
'::exercise-16':'Shows every discounted reward/penalty inequality and its sign hypothesis, then checks both upper-slope action branches and the erroneous negative-bound counterexample.',
'::exercise-17':'Substitutes every requested discount/horizon value, explains the shifted exponential horizon scaling, and derives the large-time-constant expansion term by term.',
'::exercise-18':'Works complete safe and unsafe trajectory timing, strict/tie thresholds, the theorem constants and intermediate exact-value bound, and the changed-discount case.',
'::exercise-19':'Derives supremum-expectation equality under simultaneous attainment, weak duality, the multiplier ray and continuity, contrasts all/some maximizers and qualifications, and analyzes update termination with its explicit feedback assumptions.',
'::exercise-20':'Proves support restriction and the KL uniform entropy bound, substitutes both temperatures and decade changes and limits the constants to their illustrative sufficient-bound scope.',
}
rows=[]
for e in baseline['exercises']:
    key=e['anchor'] if e['anchor'] is not None else '::exercise-'+str(e['ordinal'])
    assert key in replacements or key in retained,key
    row={'inventory_key':e['inventory_key'],'source_file':e['source_file'],'original_solution_sha256':e['solution']['sha256'],
         'decision':'replace' if key in replacements else 'retain','thoroughness_rationale':reasons.get(key,retained.get(key))}
    if key in replacements:row['replacement_html']=replacements[key]
    rows.append(row)
data=(json.dumps({'status':'all20_authored_pending_independent_review','baseline_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exercises':rows},indent=2,ensure_ascii=False)+'\n').encode()
out=ROOT/'book/solutions/drafts/viability-thorough-solutions-v1.json'
if out.exists() and out.read_bytes()!=data:raise RuntimeError('Draft is immutable')
out.write_bytes(data);print(json.dumps({'draft':str(out.relative_to(ROOT)),'exercises':20,'replace':4,'retain':16,'sha256':hashlib.sha256(data).hexdigest()}))
