"""Prepare complete GoSafe exercise decisions, keeping existing full proofs."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
p=ROOT/'book/solutions/baseline-source90/pages/gosafe.html.json'
baseline=json.loads(p.read_bytes());replacements={};reasons={}
def add(key,reason,body):replacements[key]=body.strip()+'\n';reasons[key]=reason
add('book-m6-b1','Shows the weighted-distance and time-budget algebra with units, the failed latency test and equality interpretation.',r'''
<p><strong>1. Recompute the state distance.</strong> At reported state $(0.60,0.40)$ and backup center $(0.8,0.3)$, the distance is $D=|0.60-0.80|+(0.5\,\mathrm s)|0.40-0.30|=0.20+0.05=0.25$ metres. The state-estimation reserve is $0.02$ metres and the motion reserve is $(0.8\,\mathrm{m/s})\Delta t$.</p>
<p><strong>2. Solve the recovery inequality.</strong> The certificate requires $0.25+0.02+0.8\Delta t\le0.4$, with the numerical terms in metres and $\Delta t$ in seconds. Subtracting the fixed reserves gives $0.8\Delta t\le0.13$. Dividing by the positive motion bound gives the largest permitted total interval, $\Delta t=0.13/0.8=0.1625$ seconds.</p>
<p><strong>3. Test the proposed interval.</strong> At $0.2$ seconds, the combined estimation-plus-motion reserve is $0.02+0.8(0.2)=0.18$ metres. The distance plus reserve is $0.25+0.18=0.43$ metres, above the $0.4$ certificate, so recovery is uncertified. The budget includes observation age, computation and switching delay; a $0.16$ second sampling period leaves only $0.0025$ seconds for other delay at this state. Equality leaves zero certified clearance under the backup. A strictly positive separation specification requires a smaller interval or a larger recovery margin.</p>
''')
add('book-m6-b2','Works every coordinate difference and tests each backup separately for both states, then interprets the union and velocity dependence.',r'''
<p><strong>1. Test $(0.40,0.10)$ against the first backup.</strong> Its center is $(0.8,0.3)$ and certified clearance is $0.4$ metres. The distance is $|0.40-0.80|+0.5|0.10-0.30|=0.40+0.10=0.50$ metres. Adding the $0.10$ metre reserve gives $0.60\gt0.40$, so this backup does not certify recovery.</p>
<p><strong>2. Test the second backup independently.</strong> Its center is $(0.45,0)$ and clearance bound is $0.25$ metres. The distance is $|0.40-0.45|+0.5|0.10-0|=0.05+0.05=0.10$ metres. Including reserve gives $0.20\le0.25$, leaving certified clearance $0.25-0.20=0.05$ metres. Thus the state is covered through the second backup.</p>
<p><strong>3. Repeat at the same position with velocity $1.0$.</strong> The first distance is $0.40+0.5|1.0-0.3|=0.40+0.35=0.75$ metres, giving total $0.85\gt0.4$. The second is $0.05+0.5|1.0-0|=0.55$ metres, giving total $0.65\gt0.25$. Neither backup covers this state, despite the unchanged clearance coordinate.</p>
<p>The covered set is the union of regions with an actual certified backup witness. More backups can enlarge that union; interpolation between controllers or ignoring velocity does not follow from these separate certificates.</p>
''')
add('practice-11','Solves the sensitivity inequality one operation at a time and explicitly subtracts switching delay from the total interval budget.',r'''
<p><strong>1. Include sampled distance and motion.</strong> To cover every sampled state within distance $0.1$, the worst transferred margin is $0.3-2(0.1+\Xi)$. With $\Xi=5\Delta t$, certification requires $2(0.1+5\Delta t)\le0.3$. Dividing by $2$ gives $0.1+5\Delta t\le0.15$, subtracting $0.1$ gives $5\Delta t\le0.05$, and dividing by $5$ yields $\Delta t\le0.01$ seconds.</p>
<p><strong>2. Spend part of the budget on switching.</strong> If the same speed bound holds during a $0.004$ second delay, use $\Xi=5(\Delta t+0.004)$. The preceding algebra now bounds the total interval: $\Delta t+0.004\le0.01$. Hence the sampling interval must satisfy $\Delta t\le0.006$ seconds.</p>
<p>At either equality the worst-case transferred margin is exactly zero. A positive practical margin requires a smaller interval or stronger lower bound. Both calculations assume the sensitivity and speed bounds throughout the monitored region; omitting implementation delay would spend more geometric margin than the certificate allows.</p>
''')
add('::exercise-18','Derives the dimension-shared covering error, includes integer grid construction and exact candidate counts, and separates linear backup work from product-grid growth.',r'''
<p><strong>(a) Share the 1-norm tolerance among coordinates.</strong> A cell-centered grid with side length $h$ gives coordinate errors at most $h/2$, so $\|x-[x]_\mu\|_1\le\sum_{j=1}^s h/2=sh/2$. Thus $h\le2\mu/s$ suffices. The ideal equality spacing gives approximately $(R/h)^s=(sR/(2\mu))^s$ points.</p>
<p>For an exact equal-cell construction when the ideal spacing does not divide $R$, take $N=\lceil sR/(2\mu)\rceil$ cells per coordinate and set $h=R/N\le2\mu/s$. The cell centers form a grid with exactly $N^s$ points and the required bound, including at the domain boundary. An endpoint grid with $N$ equal intervals instead has $(N+1)^s$ points. State which convention is used before comparing exact counts.</p>
<p><strong>(b) Count the S2 candidates using cell centers.</strong> Here $R=2$, $\mu=0.05$, and $|A|=625$. For $s=2$, $N=2(2)/(2\cdot0.05)=40$, $h=2/40=0.05$, and there are $40^2=1600$ state points. The joint acquisition considers $625(1600)=1{,}000{,}000$ parameter-state candidates.</p>
<p>For $s=6$, $N=6(2)/(2\cdot0.05)=120$ and $h=2/120=1/60$. There are $120^6=2{,}985{,}984{,}000{,}000$ state points and $625(120^6)=1{,}866{,}240{,}000{,}000{,}000$ candidates, approximately $1.87\cdot10^{15}$. The finer spacing in each coordinate is necessary because the same total 1-norm tolerance is shared across more coordinates.</p>
<p><strong>(c) Count backup comparisons instead of grid candidates.</strong> GoSafeOpt compares the measured state with each of $500$ stored backup states. Computing one squared Euclidean distance uses $s$ coordinate differences, $s$ multiplications and $s-1$ additions. At $s=6$ this gives $3000$ multiplications and $2500$ additions across the library, plus comparisons or norm evaluations. With precomputed lower bounds the per-measurement work is $O(|\mathcal B_n|s)$, rather than exponential in state dimension. At $100$ measurements per second the multiplication count is about $300{,}000$ per second; actual timing still depends on implementation and processor. These comparisons avoid the full product grid, but do not prove that the stored recovery regions cover every state a global experiment might reach.</p>
''')
add('::exercise-19','Computes both ball tests and backup rankings explicitly, then derives the two-error distance correction and its single-comparison probability.',r'''
<p><strong>(a) Solve each boundary inequality for distance.</strong> The condition is $l_n(a_s)\ge L_x(\|x-x_s\|+\Xi)$. Since $L_x=2\gt0$, this gives radius $l_n(a_s)/2-0.05$. Backup 1 has radius $0.5/2-0.05=0.20$, and backup 2 has radius $0.3/2-0.05=0.10$.</p>
<p><strong>(b) Check coverage and then select a backup.</strong> At $x=(0.2,0.05)$ the distances are</p>
<div class="math-block">$$d_1=\sqrt{0.2^2+0.05^2}=\frac{\sqrt{17}}{20}\approx0.206155,\qquad d_2=\sqrt{(0.2-0.3)^2+(0.05-0.1)^2}=\frac{\sqrt5}{20}\approx0.111803.$$</div>
<p>Both exceed their radii, so no pair passes the monitored boundary condition and the switch triggers. Equation 12 then compares the immediate backup margins $l_n(a_s)-L_xd_s$. They are $0.5-\sqrt{17}/10\approx0.087689$ and $0.3-\sqrt5/10\approx0.076393$. The first is larger, so backup $a_1$ is selected. Both are nonnegative in this numerical example. A full switching guarantee also requires the preceding monitored history and its motion bound, not just the current distances.</p>
<p><strong>(c) Include both measurement errors.</strong> Let $y=x+\varepsilon$ and $y_s=x_s+\varepsilon_s$ be the measured current and stored states. The triangle inequality gives $\|x-x_s\|\le\|y-y_s\|+\|\varepsilon\|+\|\varepsilon_s\|$. On the event that both errors have norm at most $0.01$, the extra distance allowance is $0.02$, not $0.01$. Thus use $\Xi'=0.05+0.02=0.07$, giving measured-state radii $0.25-0.07=0.18$ and $0.15-0.07=0.08$.</p>
<p>Each small-error event has probability at least $\sqrt{1-\delta_2}$ and the two errors are independent, so their intersection has probability at least $(\sqrt{1-\delta_2})^2=1-\delta_2$. This is the conservative probability for one comparison. A run with many comparisons requires a simultaneous error event or additional failure-budget accounting, and must also include the separate GP confidence event.</p>
''')
retained={
'practice-1':'Computes every sampled margin and the intersample violating margin, then explains why sample or terminal safety is insufficient.',
'practice-2':'Derives the radius and both interval endpoints, checks the query distance and independently evaluates its transferred lower margin.',
'practice-3':'Shows the integral displacement inequality for every intersample time, substitutes both intervals and states the required whole-interval speed premise.',
'practice-4':'Counts both Cartesian products with all dimension powers and explains what backup learning avoids and what still requires a certificate.',
'practice-5':'Checks each query against both intervals and identifies the uncertified gap in the enclosing interval.',
'practice-6':'Uses autonomous uniqueness to identify the restarted suffix and an infimum over fewer times to transfer the constraint; missing state/clock failure modes are explicit.',
'practice-7':'Exhibits all reach and return paths and the trap obstruction, distinguishing pointwise safety from reversibility.',
'practice-8':'Computes both joint probabilities and equal budgets with no independence and explains that time-uniform bands already cover rounds.',
'practice-9':'Displays the triangle inequality and every Lipschitz lower-bound step for all constraints under one backup, while retaining the pre-switch safety obligation.',
'practice-10':'Uses an actual retained witness and monotone minimum lower bounds to prove inclusion, then explains retries and stationarity assumptions.',
'practice-12':'Separates safety of interruption/backup from discoverability and explicitly applies the missing-coverage example to the inaccessible better island.',
'::exercise-15':'Proves suffix equality with uniqueness, subset minimum and cost-integral decomposition, explaining precisely why additive budgets do not compose across an unknown prefix.',
'::exercise-16':'Shows the whole intersample Lipschitz bound and every triangle step at the trigger state, deriving the negative uncovered margin when motion reserve is omitted.',
'::exercise-17':'Works every reach/return iterate, fixed point and intersection; explains delayed admission of s4 and the trap or added-return-edge cases.',
'::exercise-20':'Proves inclusion using retained backup and monotone confidence witnesses, then connects changed coverage to retry removal and the discoverability argument.',
}
rows=[]
for e in baseline['exercises']:
    key=e['anchor'] if e['anchor'] is not None else '::exercise-'+str(e['ordinal'])
    assert key in replacements or key in retained,key
    row={'inventory_key':e['inventory_key'],'source_file':e['source_file'],'original_solution_sha256':e['solution']['sha256'],'decision':'replace' if key in replacements else 'retain','thoroughness_rationale':reasons.get(key,retained.get(key))}
    if key in replacements:row['replacement_html']=replacements[key]
    rows.append(row)
data=(json.dumps({'status':'all20_authored_pending_independent_review','baseline_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'exercises':rows},indent=2,ensure_ascii=False)+'\n').encode()
out=ROOT/'book/solutions/drafts/gosafe-thorough-solutions-v1.json'
if out.exists() and out.read_bytes()!=data:raise RuntimeError('Draft is immutable')
out.write_bytes(data);print(json.dumps({'draft':str(out.relative_to(ROOT)),'exercises':20,'replace':5,'retain':15,'sha256':hashlib.sha256(data).hexdigest()}))
