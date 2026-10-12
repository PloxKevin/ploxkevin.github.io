from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
RAW=Path('/tmp/pages27-supplemental-archives3-independent-modules-code-review-v1.json')
DEST=ROOT/'book/coverage/checks/pages27-supplemental-archives-helper-independent-modules-review-v1.json'
FOLDER=ROOT/'book/coverage/checks/future27-core/original-pages27-supplemental-archives-code-independent-modules-v1'
assert not DEST.exists() and not FOLDER.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p)}
j=json.loads(RAW.read_bytes());assert j['errors']==[] and j['real_read_only_prepare_passed']is True
for n,h in j['closed_evidence_sha256'].items():
    p=Path(n);p=p if p.is_absolute()else ROOT/p
    assert sha(p)==h,n
files=[Path('/tmp/check-pages27-supplemental-archives3-independent-modules-v1.py'),Path('/tmp/run-pages27-supplemental-archives3-independent-modules-v1.py'),Path('/tmp/pages27-supplemental-archives3-independent-modules-code-findings-v1.json'),Path('/tmp/pages27-supplemental-archives3-independent-modules-code-actual-v1.json'),Path('/tmp/pages27-supplemental-archives3-independent-modules-code-actual-v1.log'),RAW,Path(__file__)]
aliases={};FOLDER.mkdir()
for p in files:
    q=FOLDER/p.name;q.write_bytes(p.read_bytes());assert sha(q)==sha(p);aliases[str(p)]=ref(q)
CAT=FOLDER/'original-closed-byte-aliases-v1.json'
CAT.write_text(json.dumps({'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_closed_byte_aliases':aliases,'scope':'Exact original independent reader bytes; no original review body/time/status edits.'},indent=2)+'\n')
out=dict(j);out['entire_original_independent_review_body_and_time']=j
out['original_closed_byte_aliases']=aliases;out['original_byte_alias_catalog']=ref(CAT)
for key in ('actual_independent_reader_execution','actual_independent_checker','actual_independent_reader_runner','actual_independent_reader_raw_log'):
    r=j[key];out[key]=aliases[r['file']];assert out[key]['sha256']==r['sha256']
out['closed_evidence_sha256']={}
for n,h in j['closed_evidence_sha256'].items():
    target=aliases[n]['file']if n in aliases else n
    assert not Path(target).is_absolute();out['closed_evidence_sha256'][target]=h
out['closed_evidence_sha256'].update({r['file']:r['sha256']for r in aliases.values()})
out['closed_evidence_sha256'][str(CAT.relative_to(ROOT))]=sha(CAT)
for n,h in out['closed_evidence_sha256'].items():assert sha(ROOT/n)==h,n
DEST.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'peer':ref(DEST),'catalog':ref(CAT),'fixture_count':j['fixture_count'],'prospective_bytes':j['independent_prospective_website_bytes'],'with_report_reserve':j['independent_prospective_bytes_with_native_report_and_reserve']}))
