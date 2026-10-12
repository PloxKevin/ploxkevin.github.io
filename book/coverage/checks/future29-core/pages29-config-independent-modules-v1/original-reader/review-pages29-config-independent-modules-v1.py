from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,ast,subprocess
R=Path('/home/oxrexkevin/SafetyBased');P=R/'reports/book/publication-repo'
H=R/'book/coverage/checks/root_prepare_pages29_config_v1.py'
O=Path('/tmp/pages29-config-independent-modules-peer-v1.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':sha(p)}
assert not O.exists()
s=H.read_text();tree=ast.parse(s)
values={t.id:ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)for t in n.targets if isinstance(t,ast.Name)and t.id in ['BEFORE','HEAD','BUDGET','HEADER']}
assert values['BUDGET']==850_000_000
assert sha(P/'_config.yml')==values['BEFORE']=='1f8ac723695777fc029ec267efab2141978b11f3c8b0604aebcfb9d9d953e7bd'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==values['HEAD']=='fa1e92e55ea0b8fac9ba30ef2b0450b5e5281702'
original=(P/'_config.yml').read_text();old={line[4:]for line in original.splitlines()if line.startswith('  - ')}
assert len(old)==156 and original==values['HEADER']+''.join('  - '+n+'\n'for n in sorted(old))
assert 'verification/lean' in old
additions={'reports/full-coverage/checkpoint-29','reports/full-coverage/checkpoint-28-manifest.json','reports/full-coverage/checkpoint-28-selection.json','reports/full-coverage/lean-checkpoint-28','reports/full-coverage/browser-artifacts-27','reports/full-coverage/owner28-originals-before-owner29-integration-v1','book/coverage/checks/future29-core','book/coverage/checks/future29-foundations','book/coverage/checks/future29-applied','book/coverage/checks/applied-future29','book/coverage/checks/modules-future29',*['book/coverage/inventory-'+side+'-correction'+str(i)+'.json'for i in range(61,66)for side in ['before','after']]}
assert len(additions)==21 and not old.intersection(additions)
for n in additions:assert n in s or n.startswith('book/coverage/inventory-')
for required in ['reports/full-coverage/lean-checkpoint-29','reports/full-coverage/browser-artifacts-29','SafeLearning/lipsdp.html','book/coverage/inventory.json','book/coverage/modules.json','reports/full-coverage/checkpoint-29-manifest.json','reports/full-coverage/checkpoint-29-selection.json']:
 assert not any(required==n or required.startswith(n+'/')for n in old|additions),required
assert 'all(sha(ROOT, n) == sha(PUB, n) == h' in s
assert 'for n, h in required.items(): assert kept(n, exclusions) and sha(PUB, n) == h' in s
assert "(29, 145, 20, 125)" in s and "{'reviewed': 4663, 'pending': 8111}" in s
assert "1197" in s and "10114" in s and "fresh_kernel_replay" in s and "== 11" in s
assert "reused_identical_module_and_transitive_local_imports" in s and "== 1186" in s
assert "base = included-len(original)+len(after)+len(original)" in s
assert "base+len(encoded(result)) <= BUDGET" in s
assert "with p.open('xb')" in s and "if not args.apply:" in s
result={'status':'passed_independent_pages29_archival_configuration_full_code_review','errors':[],'reviewer':'/root/modules_finish28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'entire102line_source_read':True,'original156_literal_exclusions_exact':True,'new21_literal_exclusions_reviewed':sorted(additions),'future_required_1197_audit_or_publication_staging_assumed_passed':False,'producer_or_readiness_invoked':False,'synthetic_fixtures_run':False,'facts':[
 'The current immutable metadata HEAD and exact existing156-line exclusion set are pinned before any writes. Only21 literal archive exclusions are added, with no wildcard/path traversal or outside-publication route permitted.',
 'Current65 site31 assets, live inventory/corrections/five ledgers and current29 audit/manifest/selection/browser48 captures remain included. All1197 selected Lean sources remain exact in Git under the prior verification/lean website exclusion; historical audit and source-history archives remain in Git.',
 'The code requires1197 source hashes/10114 names and axiom entries, allowed standard3, exact11 fresh and1186 reused checks, successful current manifest report hash, current global4663/8111 ledger integrity and actual browser20fresh125retained source fingerprints. Future producer/audit/staged files are mandatory prerequisites; this review does not certify those executions.',
 'The850MB calculation replaces the current configuration byte count, includes the exact old-config backup and iterates the bounded result-report encoded size to a fixed point. It records the actual included bytes before mutation; no size is claimed before real staging.',
 'Fresh exclusive-create original-config backups and result reports are written in Root and PUB; only the PUB config changes. The result explicitly leaves real Pages/live delivery pending and whole coverage false.'
 ],'actual_old_config':{'file':'reports/book/publication-repo/_config.yml','sha256':values['BEFORE']},'actual_publication_HEAD':values['HEAD'],'coverage_complete':False,'actual_finalizer':None}
O.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'peer':str(O),'sha256':sha(O),'helper':ref(H),'errors':[]}))
