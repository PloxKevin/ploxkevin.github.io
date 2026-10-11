from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
R=Path('/home/oxrexkevin/SafetyBased')
B=R/'book/coverage/checks/future24-nn-source52'
D=B/'original-tmp-v1'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':str(p.relative_to(R)),'sha256':H(p)}
def put(p,d):
 assert not p.exists(),p
 p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def main():
 proposal=Path('/tmp/modules-nn-tanh-precision-temporal-scope-proposal52-v1.json')
 peer=Path('/tmp/modules-nn-tanh52-proposal-independent-foundations-semantic-and-parser-review-v3.json')
 assert H(proposal)=='ed3048a29f91b4f68201af308429831bc094e560db99f48a8b6ffb19851ff9fe'
 assert H(peer)=='06b0bf523849ccd111594222f8e816350f54fc35a0c2447287727993882155a4'
 p=json.loads(proposal.read_text());v=json.loads(peer.read_text())
 assert v['proposal_text_approved'] and not v['whole_exercise_or_material_unit_approved'] and v['errors']==[]
 inv=R/p['inventory'];assert H(inv)==p['inventory_sha256']==H(R/'book/coverage/inventory.json')
 assert H(R/p['source'])==p['source_sha256_before']
 paths={proposal,peer,Path('/tmp/modules-review-actual-execute23.py')}
 for pattern in ['modules-tanh52*','run-modules-tanh52*']:
  paths.update(x for x in Path('/tmp').glob(pattern) if x.is_file())
 for folder in [Path('/tmp/modules-tanh52-precision-scope-proposal-v1'),Path('/tmp/modules-tanh52-precision-scope-proposal-v2')]:
  paths.update(x for x in folder.glob('*.html') if x.is_file())
  q=folder/'simulation/book/coverage/inventory.json'
  if q.exists():paths.add(q)
 paths.add(Path(v['independent_fresh_full29_page_parser']['simulation_inventory']['file']))
 D.mkdir(parents=True,exist_ok=True);aliases={}
 for old in sorted(paths):
  assert old.is_file(),old
  new=D/old.relative_to('/tmp');new.parent.mkdir(parents=True,exist_ok=True)
  if new.exists():assert new.read_bytes()==old.read_bytes()
  else:new.write_bytes(old.read_bytes())
  assert H(new)==H(old)
  aliases[str(old)]=ref(new)
 context=v['direct_exact_local_Section3_context'];loc=B/'nn-in-the-loop-source51-section3-located-lines271-307.txt'
 assert not loc.exists();loc.write_text(context['exact_lines'])
 assert (R/context['file']).read_text().splitlines(keepends=True)[270:307]==loc.read_text().splitlines(keepends=True)
 catalog=B/'approved-source52-proposal-original-byte-alias-catalog-v1.json'
 put(catalog,{'schema_version':1,'status':'approved_read_only_source52_proposal_and_original_author_independent_failure_history_exact_byte_alias_catalog','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'original_proposal':aliases[str(proposal)],'original_independent_semantic_primary_and_parser_peer':aliases[str(peer)],'original_absolute_path_byte_aliases':aliases,'located_local_section3_excerpt':ref(loc),'primary_source_provenance':'The original independent peer retains primary URL/hash/located excerpts. No full external paper is copied by this archive.','entire_original_proposal_body_and_time':p,'entire_original_peer_body_and_time':v,'current_inventory':{'file':str(inv.relative_to(R)),'sha256':H(inv)},'proposed_source_sha256_before':p['source_sha256_before'],'proposed_source_sha256_after':p['proposed_source_sha256_after'],'only_changed_literal_keys':v['only_changed_literal_keys'],'whole_exercise_remains_pending':True,'live_source_inventory_or_owner_mutated':False})
 print(json.dumps({'catalog':ref(catalog),'aliases':len(aliases),'proposal':aliases[str(proposal)],'peer':aliases[str(peer)]}))
if __name__=='__main__':main()
