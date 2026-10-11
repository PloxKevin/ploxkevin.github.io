from pathlib import Path
import json,hashlib,re,copy
from datetime import datetime,timezone
R=Path('/home/oxrexkevin/SafetyBased'); H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
P=lambda p:Path(p) if Path(p).is_absolute() else R/p
J=lambda p:json.loads(P(p).read_text())
refs={}
def ref(p,h=None):
 x=P(p); a=H(x); assert h is None or a==h,(p,a,h);refs[str(p)]=a;return {'file':str(p),'sha256':a}
def zero(d):
 ks=[k for k in ['exit_code','actual_exit_code'] if k in d];assert ks and all(type(d[k])is int and d[k]==0 for k in ks)
oldp='/tmp/landscape15-source52-twelve-new-bodies-independent-foundations-full-whole-review26-v1.json'; oldref=ref(oldp,'ad3778c3f5ff5e3b93c04b6d29215f5c302b19c5fbdfb63b09e65ba18e4af66b');old=J(oldp);assert old['whole_exercise_approved'] and old['missing_clauses']==[] and old['errors']==[]
ref(old['inventory']['file'],old['inventory']['sha256']);inv=J(old['inventory']['file']);htmlref=ref(old['source_html']['file'],old['source_html']['sha256']);html=P(htmlref['file']).read_text()
for s in old['full_context'].values():assert s in html
rows={r['key']:r for r in inv['material_source_units']};keys=['landscape.html::node-1285','landscape.html::node-1294','landscape.html::node-1297'];hs=['7d9ecee3841b2180bd1eaba4af7685e4162c4670263c9294c6a063f617a860f3','da47d5ec9c120c1d0956ca5732873bf00eb1d8ae34c5254c8c42ae024fe5daa0','189c12a35624571704c57f31c51dfe32be5ef8f5c79ecc4c01bab8829e73846b']
for k,h in zip(keys,hs):assert rows[k]['source_sha256']==htmlref['sha256'] and rows[k]['text_sha256']==h and hashlib.sha256(rows[k]['source_text'].encode()).hexdigest()==h
sources={}
for p,v in old['selected24_sources_and_entire_bodies'].items():
 ref(p,v['sha256']);assert P(p).read_text()==v['entire_source_text_read'];sources[p]=P(p).read_text()
wp='book/coverage/checks/future26-core/wind-classification/root-wind-classification26-canonical-readiness-v1.json';wref=ref(wp);w=J(wp);ref(w['source']['file'],w['source']['sha256']);assert P(w['source']['file']).read_text()==old['complete_wind_source_body'];sources[w['source']['file']]=P(w['source']['file']).read_text();ref(w['source_snapshot']['file'],w['source_snapshot']['sha256']);ref(w['original_full_source_peer']['file'],oldref['sha256'])
for r in w['actual_canonical_pair']:
 ref(r['file'],r['sha256']);zero(J(r['file']));ref(r['log']['file'],r['log']['sha256'])
cp='book/coverage/checks/applied-future26/cvar-fractional-selector/one-source8-canonical-paired-build-readiness-v1.json';cref=ref(cp);c=J(cp);assert c['public_theorem_count']==8 and c['actual_canonical_execution_count']==2
cr=old['cvar_independent_eight_body_component_peer'];ref(cr['file'],cr['sha256']);cvpeer=J(cr['file'])
for s in c['proof_sources']:
 ref(s['source']['file'],s['source']['sha256']);assert P(s['source']['file']).read_text()==cvpeer['complete_source_body'];sources[s['source']['file']]=P(s['source']['file']).read_text()
 for a in s['actual_canonical_pair']:
  ref(a['record']['file'],a['record']['sha256']);actual=J(a['record']['file']);assert actual==a['entire_original_actual_record'];zero(actual)
  for name in ['raw_log','source_snapshot']:ref(a[name]['file'],a[name]['sha256'])
groups=old['eight_literal_clause_decisions']; assert len(groups)==8 and [g['clause'] for g in groups]==list(range(1,9)) and all(g['missing_clauses']==[] and g['remaining_gaps']==[] for g in groups)
caveat=old['empirical_vs_population_caveat'];direct={}
for name in dict.fromkeys([n for g in groups for n in g['lean_declarations']]+caveat['lean_declarations']):
 short=name.rsplit('.',1)[1];ns=name.rsplit('.',1)[0];found=[p for p,body in sources.items() if ('namespace '+ns)in body and re.search(r'\b(?:theorem|lemma)\s+'+re.escape(short)+r'\b',body)];assert len(found)==1,(name,found);direct[name]=found[0]
units=[]
for k in keys:
 r=rows[k];iscaveat=k.endswith('1294');gs=[copy.deepcopy(caveat)] if iscaveat else copy.deepcopy(groups);names=list(dict.fromkeys(n for g in gs for n in g['lean_declarations']));hyp=list(dict.fromkeys(h for g in gs for h in g['hypotheses']))
 units.append({'source_unit_key':k,'entire_inventory_record':r,'source_text':r['source_text'],'source_text_sha256':r['text_sha256'],'decision':'approved_complete_conditional_modeling_caveat_nonformal' if iscaveat else 'approved_complete_whole_mathematical_literal','status':'not_formalizable' if iscaveat else 'proved','whole_literal_approved':True,'components':gs,'lean_declarations':names,'hypotheses':hyp,'reason':caveat['reason'] if iscaveat else 'The complete eight-item literal is covered by the exact eight original whole-exercise clause decisions below, with their original formal declarations, hypotheses and reasons unchanged. This is a physical-unit interface supplement; no new semantic decision or unspecified physical dynamics proof is inferred.','missing_clauses':[],'remaining_gaps':[],'reviewed_at_utc':old['reviewed_at_utc'],'reviewer':old['reviewer'],'classification_scope':'Conditional modeling and inference advice. The existing five declarations supply empirical-law identities and genuine population counterexamples; this literal is not a fresh sampling guarantee.' if iscaveat else 'All eight mathematical classification clauses, under the exact original assumptions.'})
out={'status':'independent_landscape15_three_exact_physical_unit_scope_supplement_passed','errors':[],'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'independent_foundations','original_whole_exercise_peer':oldref,'entire_original_whole_peer_body_time_and_decisions_unchanged':old,'inventory':old['inventory'],'source_html':htmlref,'material_units':units,'original_eight_groups_and_empirical_caveat_preserved_exact':True,'direct_declaration_sources':direct,'canonical_wind_readiness':wref,'canonical_CVaR_readiness':cref,'actual_canonical_records_checked':4,'scope':'Narrow exact physical-unit and canonical-byte interface to the already complete ad377 semantic review. No semantic redecision, current owner mapping, selected proof, HTML, inventory or aggregate claim. The conditional caveat is explicitly classified rather than promoted to a new sampling theorem.','closed_evidence_sha256':refs}
q=Path('/tmp/landscape15-three-physical-units-independent-foundations-scope-supplement26-v1.json');assert not q.exists();q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'passed','units':keys,'declarations':len(direct),'review_sha256':H(q)}))
