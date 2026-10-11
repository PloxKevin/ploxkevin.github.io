"""TMP-only precise assumption correction proposal; current Source53 stays held."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
root=Path('/home/oxrexkevin/SafetyBased');source=root/'SafeLearning/lyapunov-mpc.html'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source)=='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
old=source.read_text();new=old
replacements=[
(r'There are a feedback $\kappa(x,z,v)$, a <em>$\delta$-Lyapunov function</em> $V_\delta(x,z,v)\ge0$ with $V_\delta(z,z,v)=0$,',
 r'There are a feedback $\kappa:X\times X\times U\to\mathbb R^m$, a <em>$\delta$-Lyapunov function</em> $V_\delta:X\times X\times U\to\mathbb R_{\ge0}$ continuous in its first state argument, with $V_\delta(z,z,v)=0$ for $z\in X$, $v\in U$,'),
(r'such that, whenever $V_\delta(x,z,v)\le\delta_{\rm loc}$,',
 r'such that, for $(x,z,v)\in X\times X\times U$ and $(z^+,v^+)\in X\times U$, whenever $V_\delta(x,z,v)\le\delta_{\rm loc}$,'),
(r'the squared tracking error shrinking by the factor $\rho$ per step.<br>',
 r'the squared tracking error shrinking by the factor $\rho$ per step where those domain conditions hold. Unadorned vector norms here are Euclidean; the disturbance norm $\|d\|_\infty$ is the infinity input norm.<br>'),
(r'<em>Assumption 2.</em> $\|f(x,u+d)-f(x,u)\|\le\lambda\|d\|_\infty$',
 r'<em>Assumption 2.</em> Choose a positive Lipschitz bound $\lambda\gt0$ with $\|f(x,u+d)-f(x,u)\|\le\lambda\|d\|_\infty$'),
(r'so the re-planned trajectory starts within $V_\delta\le c_{\delta,u}\lambda^2\eta^2\le\delta_{\rm loc}$ of the old plan: Assumption 3 is exactly what keeps this inside the region where the tracking certificate holds. Afterwards',
 r'The first disturbed successor must first be kept in $X$ by the constraint tightening. Continuity of $V_\delta$ along the segment from the nominal successor (where it is zero) then lets the local quadratic upper bound establish $V_\delta\le c_{\delta,u}\lambda^2\eta^2\le\delta_{\rm loc}$ without assuming its own locality premise. At each subsequent contraction step the state and shifted-input domain conditions must also hold. Under those conditions'),
]
for before,after in replacements:
 assert new.count(before)==1,before
 new=new.replace(before,after,1)
assert old.count('\n')==new.count('\n')
candidate=Path('/tmp/lyapunov-mpc-source54-continuity-and-domains-proposal-v1.html');record=Path('/tmp/root-source54-continuity-and-domain-proposal-v1.json')
assert not candidate.exists() and not record.exists()
with candidate.open('x') as f:f.write(new)
primary=root/'reports/full-coverage/source-history/approved-mpc-scenario-scope-correction53-20261011/semantic-original-root/sources/text/hertneck.txt.log'
body={'status':'tmp_source54_correction_proposal_requires_independent_full_source_review_and_new_protected_application',
 'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':str(Path(__file__)),'sha256':sha(Path(__file__))},
 'current_source53':{'file':'SafeLearning/lyapunov-mpc.html','sha256':sha(source)},
 'candidate_only':{'file':str(candidate),'sha256':sha(candidate)},
 'primary_original':{'file':str(primary.relative_to(root)),'sha256':sha(primary),'read_full_scope_lines':[166,234]},
 'exact_five_replacements':[{'before':a,'after':b} for a,b in replacements],
 'scope':'TMP proposal only. Restores first-argument continuity and X/X/U plus shifted z+/v+ domains from the full original Assumption1, makes vector norm conventions explicit, chooses a positive valid Lipschitz upper bound before its reciprocal, and states the bootstrap/domain prerequisites. No current Source53 asset, inventory, ledger, frozen26 input or status was changed. The derived finite-horizon shifted-plan certificate and whole Exercise18/physical1387 remain pending. No independent mathematical approval or actual Source54 parser/application/Lean check is inferred.'}
with record.open('x') as f:f.write(json.dumps(body,indent=2)+'\n')
assert sha(source)=='5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af'
print(json.dumps({'proposal':str(record),'sha256':sha(record),'candidate':str(candidate),'candidate_sha256':sha(candidate)}))
