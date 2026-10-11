from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();real=lambda p:Path(p)if Path(p).is_absolute()else R/p
O=Path('/tmp/applied27-source55-identity-v1/applied-audit27-source55-identity-additions-v1-reviewed.json');C=O.parent/'reviewed-offer-completed-finalization-evidence-v1.json';d=json.loads(O.read_text());c=json.loads(C.read_text());assert H(O)=='b98f3690edc0a88473258545ff2ae8f18d2cc786da08aa9d5fd483d536f3514d';assert c['errors']==[] and c['final_reviewed_offer']['sha256']==H(O)
refs=dict(d['required_evidence_artifacts_sha256'])
for f,h in c['closed_evidence_sha256'].items():assert f not in refs or refs[f]==h;refs[f]=h
refs[str(C)]=H(C)
for f in ['/tmp/prepare-applied27-current55-reviewed-offer-original-byte-pack-v1.py','/tmp/run-applied27-current55-reviewed-offer-original-byte-pack-v1.py']:refs[f]=H(f)
P=Path('/tmp/applied27-current55-reviewed-offer-original-byte-pack-v1');assert not P.exists();P.mkdir();aliases={};rootrefs={}
for i,(f,h)in enumerate(sorted(refs.items())):
 src=real(f);assert H(src)==h
 if src.is_relative_to(R):rootrefs[f]=h;continue
 dest=P/'original-tmp'/(str(i).zfill(3)+'-'+src.name);dest.parent.mkdir(exist_ok=True);dest.write_bytes(src.read_bytes());assert H(dest)==h;aliases[f]={'file':str(dest),'sha256':h}
p=P/'applied27-current55-reviewed-offer-original-byte-pack-v1.json';p.write_text(json.dumps({'status':'passed_exact_original_tmp_byte_pack_and_immutable_root_reference_closure','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'final_reviewed_offer':{'file':str(O),'sha256':H(O)},'entire_original_final_reviewed_offer_body_and_time':d,'completed_finalization_supplement':{'file':str(C),'sha256':H(C)},'original_closed_byte_aliases':aliases,'unchanged_root_evidence_sha256':rootrefs,'full_closed_original_evidence_sha256':refs,'scope':'TMP-only exact byte copies of every absolute TMP closure input and exact immutable ROOT references; final offer and all old semantic bodies/times unchanged. No eligible canonical offer, live owner/source/proof/PUB/Git mutation.'},indent=2)+'\n');print(json.dumps({'pack':str(p),'sha256':H(p),'exact_tmp_aliases':len(aliases),'unchanged_root_refs':len(rootrefs),'entire_closure':len(refs)}))
