from pathlib import Path
from datetime import datetime,timezone
import ast,copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased')
N='book/coverage/checks/root_prepare_pages23_config_v2.py'
O=Path('/tmp/pages23-config-v2-independent-modules-code-review-v1.json')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(R/N).read_text();tree=ast.parse(s)
assert h(R/N)=='7256ceed8c875961e8ecc097caf070c9727be2b9099a1c07e112d0e90af97331'
assert not O.exists()
constants={}
for node in tree.body:
    if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
        try:constants[node.targets[0].id]=ast.literal_eval(node.value)
        except (ValueError,TypeError):pass
assert constants['INVENTORY_SHA']=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
assert h(R/'book/coverage/inventory-after-correction51.json')==constants['INVENTORY_SHA']
assert h(R/'reports/full-coverage/checkpoint-22-manifest.json')==constants['MANIFEST22_SHA']
assert constants['PREVIOUS22_SHA']=='443a2c117d1caf7d3d0236235b15af1cafc48cfd60ab8f9b60ef5a9c7909e41a'
assert h(R/'reports/book/publication-repo/_config.yml')==constants['PREVIOUS22_SHA']
for n,d in constants['SOURCE51_REVISIONS'].items():assert h(R/n)==d
assert constants['OWNERS']==['core','foundations','applied','modules']
assert len(constants['APPLIED_UNSELECTED_METADATA'])==3
for fragment in (
    'audit["status"] == "passed" and audit["proof_file_count"] == 1131 and audit["theorem_count"] == 9193',
    'all(check["exit_code"] == 0 for check in audit["checks"])',
    'all(audit["proof_sha256"][name] == old_audit["proof_sha256"][name] for name in old_manifest["proof_files"])',
    'working_ledger == frozen_ledger',
    'git", "ls-files", "-z", "--", older_audit_archive',
    'git", "diff", "--quiet", "HEAD", "--", older_audit_archive',
    'assert included_bytes < 900_000_000',
    'with PREVIOUS.open("xb")',
    'CONFIG.write_text(new_config)',
    'assert kept("reports/full-coverage/lean-checkpoint-22/verification-original.json")',
):assert fragment in s,fragment
# Only the named publication config and new original/preparation records are written.
writes=[]
for n in ast.walk(tree):
    if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ('open','write_text','write_bytes'):
        base=ast.unparse(n.func.value)
        if n.func.attr=='open':
            if n.args and isinstance(n.args[0],ast.Constant) and any(t in n.args[0].value for t in 'wax'):writes.append(base)
        else:writes.append(base)
assert set(writes)=={'PREVIOUS','PREVIOUS_RECORD','CONFIG','REPORT'},writes
# Execute only the pure path inclusion function on independent fixtures.
f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='kept')
scope={'excluded':{'reports/full-coverage/lean-checkpoint-21','reports/full-coverage/checkpoint-23','book/coverage/inventory-after-correction51.json'}}
exec(compile(ast.Module(body=[f],type_ignores=[]),'<pure-path-fixtures>','exec'),scope)
kept=scope['kept']
fixtures={
 'reports/full-coverage/lean-checkpoint-21/verification-original.json':False,
 'reports/full-coverage/lean-checkpoint-21':False,
 'reports/full-coverage/lean-checkpoint-210/verification-original.json':True,
 'reports/full-coverage/lean-checkpoint-22/verification-original.json':True,
 'reports/full-coverage/lean-checkpoint-23/verification-original.json':True,
 'SafeLearning/nn-in-the-loop.html':True,
 'book/coverage/inventory.json':True,
 'book/coverage/inventory-after-correction51.json':False,
}
for n,v in fixtures.items():assert kept(n) is v
# Independent model of the exact three metadata removals preserves every claim.
base={'proof_files':{'kept':{'sha256':'a'},**{n:{'sha256':'unused'} for n in constants['APPLIED_UNSELECTED_METADATA']}},'exercises':[{'status':'partial','hypotheses':['premise']}],'material_claims':[{'status':'proved','correspondence':'original','reviewed_at':'old'}]}
normalized=copy.deepcopy(base);normalized['proof_files']={n:v for n,v in normalized['proof_files'].items() if n=='kept'}
assert normalized['exercises']==base['exercises'] and normalized['material_claims']==base['material_claims']
assert set(base['proof_files'])-set(normalized['proof_files'])==set(constants['APPLIED_UNSELECTED_METADATA'])
out={'status':'independent_pages23_configuration_v2_code_mechanics_review_passed_requires_actual_output_peer','checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':N,'sha256':h(R/N)},'preserved_unexecuted_original_helper':{'file':'book/coverage/checks/root_prepare_pages23_config_v1.py','sha256':h(R/'book/coverage/checks/root_prepare_pages23_config_v1.py')},'pure_fixture_count':len(fixtures)+1,'mechanical_findings':['Requires actual23 manifest, 1131 proof files/9193 passing theorem checks and preserved1113 prior source hashes before preparing config.','Keeps current51 all31 assets, inventory, frozen23 ledgers and actual23 audit reports; exact working/frozen normalization permits only three explicitly manifest-listed unused Applied metadata rows.','Retains every older21 audit byte in ROOT/PUB with equal complete hash maps, exact tracked Git names and clean HEAD diff before excluding that literal directory from the website.','Preserves exact prior22 config and records, appends only literal paths, retains baseline22/current23 audits and enforces actual included bytes below900MB.','Writes only publication _config.yml plus three new original/preparation records; no source/owner ledger/selected proof edits.'],'errors':[],'coverage_complete':False,'scope':'Independent source and pure-fixture code review only. The preparation helper was not executed; actual config output, Pages build and live hashes need separate actual execution and peer review.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':h(O)}))
