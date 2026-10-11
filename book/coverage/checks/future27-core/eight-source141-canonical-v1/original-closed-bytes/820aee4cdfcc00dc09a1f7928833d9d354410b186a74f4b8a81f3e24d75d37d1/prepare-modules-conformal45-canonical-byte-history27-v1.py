from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/modules-conformal45-source55-full-whole-review-request27-v1.json');BASE=Path('/tmp/modules-conformal45-canonical-byte-history27-v1');OUT=BASE/'conformal45-original-source-and-history-preparation27-v1.json'
assert not BASE.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(n):return Path(n) if Path(n).is_absolute() else ROOT/n
assert sha(REQUEST)=='a7f3fb3988d41be91af9c882ee8ae295feb4b855b1ec2a12b0aec082089ed3a6'
d=json.loads(REQUEST.read_text());names=['CompleteModulesConformalContinuous27','CompleteModulesConformalLexicographic27','CompleteModulesConformalCommonUniform27'];hist=dict(d['evidence_sha256']);hist[str(REQUEST)]=sha(REQUEST);hist[str(Path(__file__))]=sha(Path(__file__))
plan={};copied={};sources=[]
for n,h in hist.items():
 p=path(n);assert p.is_file() and not p.is_symlink() and sha(p)==h,n
 target=BASE/('original-tmp' if p.parent==Path('/tmp') else 'original-root')/(p.name if p.parent==Path('/tmp') else p.relative_to(ROOT))
 assert target not in plan;plan[target]=p;copied[n]={'file':str(target),'sha256':h}
for source,name,record in zip(d['three_entire_actual_sources'],names,d['genuine_successful_standalone_records']):
 p=path(source['source']['file']);assert p.read_text()==source['entire_source']
 namespace=re.search(r'^namespace ([\w.]+)',p.read_text(),re.M).group(1);assert namespace=='SafeLearning.'+name
 sources.append({'intended_canonical_source':'verification/lean/SafeLearning/'+name+'.lean','original_source':source['source'],'prospective_exact_byte_copy':{'file':str(BASE/(name+'.lean')),'sha256':sha(p)},'public_theorem_count':source['public_theorem_count'],'all_public_declarations':source['all_public_declarations'],'original_true_tmp_standalone':record})
BASE.mkdir(parents=True)
for target,p in plan.items():
 target.parent.mkdir(parents=True,exist_ok=True)
 with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(target)==sha(p)
for row in sources:
 p=path(row['original_source']['file']);target=Path(row['prospective_exact_byte_copy']['file'])
 with target.open('xb') as f:f.write(p.read_bytes())
 assert sha(target)==row['original_source']['sha256']
result={'status':'prepared_exact_tmp_original_bytes_and_prospective_source_names_no_canonical_execution','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_full45_request':{'file':str(REQUEST),'sha256':sha(REQUEST)},'entire_original_request_body_and_time':d,'sources':sources,'sources_count':3,'public_theorem_count':45,'original_closed_byte_aliases':copied,'history_count':len(copied),'scope':'TMP-only preparation preserves every original source/trial/pass/failure/log/snapshot/runner/review/current53 mutable original byte before Source54/55 application. Full independent45 semantic peer remains pending. No canonical or named build, current55 identity, selection or owner integration claimed.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'prepared_tmp_only','packet':str(OUT),'sha256':sha(OUT),'sources':3,'public':45,'history':len(copied)}))
