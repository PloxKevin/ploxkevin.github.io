from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased')
H=R/'book/coverage/checks/root_resume_publication28_staging_v1.py';EXPECTED='1f5eb66e5825aa20754491b3ec8d9dc93711f227e8e104c0c5a7c948440d970e'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(H)==EXPECTED;ast.parse(H.read_text())
PLAN='book/coverage/checks/future28-core/root-explicit-audited28-publication-stage-plan-v1.json';assert sha(R/PLAN)=='345a89fe0be7c5dba487445194bbaf199c24cc4b2ddfe253a1d3f0a90f6fb1ad'
f=json.loads((R/'reports/full-coverage/stage-publication28-execution-v1.json').read_bytes());assert sha(R/'reports/full-coverage/stage-publication28-execution-v1.json')=='7236c9570b443ff961afe01e1db2aa4e54a5f9fce82b6bb3640e3a6dd48b3699'
assert type(f['actual_exit_code']) is int and f['actual_exit_code']==1 and f['status']=='failed'
assert f['actual_command']==['python3','book/coverage/checks/root_stage_publication28_v6.py','--plan',PLAN,'--plan-sha256',sha(R/PLAN),'--apply'] and f['actual_workdir']==str(R)
assert sha(R/f['log'])==f['log_sha256']=='875ce499854712ea800ee0454a703d152710255870032dbe641e73b2c53ef720';assert 'assert n.endswith' in (R/f['log']).read_text()
p=json.loads((R/PLAN).read_bytes());audit=json.loads((R/p['original_audit']['file']).read_bytes());manifest=json.loads((R/p['manifest']['file']).read_bytes());assert sha(R/p['original_audit']['file'])==p['original_audit']['sha256'];assert sha(R/p['manifest']['file'])==p['manifest']['sha256']
assert len(audit['proof_sha256'])==1186 and audit['theorem_count']==9896 and audit['status']=='passed'
CROWN='verification/lean/SafeLearning/CompleteModulesCrownOtherRadii28.lean';SNAPSHOT='book/coverage/checks/future28-core/current60-canonical-pairs-v1/source-snapshots/CompleteModulesCrownOtherRadii28.lean'
rows={CROWN:{119,121},SNAPSHOT:{119,121}}
for page,nums in {'barriers.html':{217,604,607},'cmdp.html':{458,509},'toolkit-gp.html':{131,146,269,409,525,691},'toolkit-lmi.html':{215,375,564},'viability.html':{583}}.items():
 n='reports/full-coverage/browser-input28-source60/SafeLearning/'+page;assert sha(R/n)==sha(R/'SafeLearning'/page)==manifest['frozen_inputs_sha256']['SafeLearning/'+page];rows[n]=nums
assert sha(R/CROWN)==sha(R/SNAPSHOT)==audit['proof_sha256'][CROWN]
checked=[]
for n,nums in rows.items():
 lines=(R/n).read_text().splitlines()
 for line in sorted(nums):assert re.search(r'[ \t]+$',lines[line-1]),(n,line)
 checked.append({'file':n,'sha256':sha(R/n),'exact_whitespace_lines':sorted(nums)})
assert sum(len(v) for v in rows.values())==19
for marker in ["assert seen==allowed_special", "assert sha(ROOT/CROWN)==sha(ROOT/SNAPSHOT)==audit['proof_sha256'][CROWN]", "hash-object','--stdin-paths','--no-filters", "n in names and sha(s.safe(ROOT,n))==sha(s.safe(PUB,n))==expected[n]", "git(['add','-f','--',REPORT])"]:assert marker in H.read_text(),marker
OUT=Path('/tmp/publication28-resume-independent-applied-findings-v1.json');assert not OUT.exists();OUT.write_text(json.dumps({'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper_sha256':EXPECTED,'full_code_read':True,'ast_syntax_passed':True,'factual_pinned_failed_native_checked':True,'factual_diagnostic_associations_checked':checked,'exact_special_diagnostic_count':19,'production_prefix_or_producer_executed':False,'git_mutation_invoked':False,'scope':'Conditional full code review and exact actual source/native provenance association. No mirror fixture suite or actual production completion claim.','inherited_failed_native_boilerplate':'Old baseline26/selection27 native summary fields remain historical; pinned actual plan selection28/audit28 control this completion.'},indent=2)+'\n');print(json.dumps({'status':'passed','findings':str(OUT),'exact_special_diagnostics':19}))
