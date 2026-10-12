from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
RAW=Path('/tmp/pages27-supplemental-archives3-actual-output-independent-modules-review-v2.json')
DEST=ROOT/'book/coverage/checks/future27-core/pages27-supplemental-archives-independent-modules-output-v1.json'
FOLDER=ROOT/'book/coverage/checks/future27-core/original-pages27-supplemental-archives-output-independent-modules-v1'
assert not DEST.exists() and not FOLDER.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(ROOT)),'sha256':sha(p)}
j=json.loads(RAW.read_bytes());assert j['errors']==[] and j['status']=='passed_independent_actual_checkpoint27_supplemental_archive_configuration' and j['excluded_count']==133
for n,h in j['closed_evidence_sha256'].items():
    p=Path(n);p=p if p.is_absolute()else ROOT/p
    assert sha(p)==h,n
files=[Path('/tmp/check-pages27-supplemental-archives3-actual-output-independent-modules-v2.py'),Path('/tmp/run-pages27-supplemental-archives3-actual-output-independent-modules-v2.py'),Path('/tmp/pages27-supplemental-archives3-actual-output-independent-modules-findings-v2.json'),Path('/tmp/pages27-supplemental-archives3-independent-modules-output-actual-v2.json'),Path('/tmp/pages27-supplemental-archives3-independent-modules-output-actual-v2.log'),RAW,Path(__file__)]
files.extend(Path(r['file'])for r in j['preserved_first_reader_failure']['original_closed_files'])
assert len(files)==len(set(files))==11
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
print(json.dumps({'peer':ref(DEST),'catalog':ref(CAT),'original_count':len(aliases),'config_sha256':j['config_sha256'],'excluded_count':j['excluded_count'],'prospective_bytes':j['prospective_website_bytes_with_current_native_outputs']}))
