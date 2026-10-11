from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json
ROOT=Path('/home/oxrexkevin/SafetyBased')
HELPER='book/coverage/checks/root_prepare_checkpoint24_documentation_v1.py'
PIN='9acef765add0d8d2ca2914d886af5ad534ba0368e66fc44d5349c567ddc6653d'
OUT=Path('/tmp/checkpoint24-documentation-helper-independent-applied-review-v1.json')
assert not OUT.exists()
sha=lambda n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest()
source=(ROOT/HELPER).read_text();assert sha(HELPER)==PIN
tree=ast.parse(source)
direct_reads={n.args[0].value for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='read' and n.args and isinstance(n.args[0],ast.Constant) and isinstance(n.args[0].value,str)}
assert 'reports/full-coverage/integration-24.json' not in direct_reads
assert 'reports/full-coverage/browser-checkpoint-24.json' not in direct_reads
assert source.index("(ROOT/'book/coverage/progress.json').write_text") < source.index('binding=read(selection')
assert "audit['status']=='passed'" in source and "ledger['mathematical_coverage_complete'] is False" in source
assert "with (ROOT/backup).open('xb')" in source and "with (ROOT/readme_backup).open('xb')" in source
assert "progress=copy.deepcopy(original)" in source and "previous_checkpoint23_delivery" in source
manual='book/coverage/checks/future24-core/root24-corrected-NN-paragraphs-manual-visual-inspection-v1.json'
body=json.loads((ROOT/manual).read_text())
assert len(body['images_sha256'])==4
for n,h in body['images_sha256'].items():assert sha(n)==h
for n,h in body['actual_capture_evidence'].items():assert sha(n)==h
assert sha(HELPER)==PIN
out={'status':'independent_code_read_requires_new_guarded_version_before_approval','approved':False,
 'checked_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/applied_next',
 'helper':{'file':HELPER,'sha256':PIN},
 'findings':[
 {'scope':'preflight of factual README claims','reason':'The helper gates audit status/counts/replay modes and frozen-ledger partial status, but does not read or gate the measured audit wrapper, actual static/browser reports, separate four-image manual report, exact Lean version, or audit/manifest/selection proof identities before making their README statements. The existing separate manual report supports the bounded rendering sentence; the composite browser report does not itself claim a new manual pass.'},
 {'scope':'all prerequisites before metadata writes','reason':'The helper writes progress.json before it reads the selection content-binding file needed by README generation. A missing or malformed binding can produce a reversible but incomplete metadata update. Read and validate every prerequisite before backups/writes in a new version.'}],
 'valid_existing_guards':['Actual audit passed/counts and every exit0','13 fresh/1131 reused replay modes','Frozen ledger integrity/errors/partial status and current inventory identity','Exact original progress and README byte backups and original progress deep copy','Previous23 delivery record retained and new24 delivery explicitly pending'],
 'separate_manual_report':{'file':manual,'sha256':sha(manual)},
 'code_execution_scope':'Actual independent read-only AST/context checker only. Root documentation helper is unexecuted; no production audit24, metadata update, publication copy or Pages result is claimed.'}
OUT.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'review':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest(),'approved':False}))
