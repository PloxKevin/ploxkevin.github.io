from pathlib import Path
from datetime import datetime,timezone
from html.parser import HTMLParser
from collections import Counter,defaultdict
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased');OUT=Path('/tmp/foundations-pending-whole-unit-families28-v1.json');assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
ownerp=ROOT/'book/coverage/foundations.json';invp=ROOT/'book/coverage/inventory.json'
held={str(ownerp):'b3de5e813f882355cd90e46d27adc4ce56351ddd51d9038a1b8c79511b365b55',str(invp):'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf'}
for p,h in held.items():assert sha(p)==h
f=json.loads(ownerp.read_bytes());i=json.loads(invp.read_bytes());units={u['key']:u for u in i['material_source_units']}
exercise=Counter(e['status']for e in f['exercises']);assert exercise=={'complete_math':119}
pending=[c for c in f['material_claims']if c['status']=='pending'];keys={k for c in pending for k in c['source_unit_keys']}
assert len(pending)==483 and len(keys)==452
class Headings(HTMLParser):
    def __init__(self):super().__init__(convert_charrefs=True);self.headings=[];self.current=None
    def handle_starttag(self,tag,attrs):
        if tag in ('h2','h3'):self.current={'tag':tag,'line':self.getpos()[0],'id':dict(attrs).get('id'),'text_parts':[]}
    def handle_data(self,data):
        if self.current is not None:self.current['text_parts'].append(data)
    def handle_endtag(self,tag):
        if self.current is not None and tag==self.current['tag']:
            h=self.current;h['text']=''.join(h.pop('text_parts')).strip();self.headings.append(h);self.current=None
pages=[]
for page in sorted({units[k]['source']for k in keys}):
    p=ROOT/page;held[str(p)]=i['source_sha256'][page];assert sha(p)==held[str(p)]
    parser=Headings();parser.feed(p.read_text());groups={};subgroups={};rows=[]
    for k in sorted(keys,key=lambda k:(units[k]['line'],k)):
        u=units[k]
        if u['source']!=page:continue
        assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
        before=[h for h in parser.headings if h['line']<=u['line']]
        h2=next((h for h in reversed(before)if h['tag']=='h2'),{'text':'Before the first main section','line':0,'id':None})
        h3=next((h for h in reversed(before)if h['tag']=='h3'and h['line']>=h2['line']),None)
        group=groups.setdefault(h2['text'],{'source_heading':h2,'pending_distinct_unit_keys':[],'pending_claim_ids':[]})
        group['pending_distinct_unit_keys'].append(k)
        claims=[c for c in pending if k in c['source_unit_keys']]
        group['pending_claim_ids'].extend(c['id']for c in claims)
        rows.append({'key':k,'source_heading':h2,'source_subheading':h3,'entire_literal_inventory_record':u,'current_pending_claim_ids':[c['id']for c in claims]})
    for g in groups.values():g['pending_distinct_units']=len(g['pending_distinct_unit_keys']);g['pending_claim_records']=len(set(g['pending_claim_ids']))
    pages.append({'source':ref(p),'pending_distinct_units':len(rows),'pending_claim_records':sum(c['source']==page for c in pending),'families_by_actual_source_h2':list(groups.values()),'full_pending_literal_catalog':rows})
future=[{'request':ref(Path('/tmp/foundations-residual17-independent-modules-full-source-review28-v1.json')),'whole_unit_keys':['primer-linalg.html::node-1288','primer-linalg.html::node-1290','primer-linalg.html::node-1293'],'new_public_bodies':17,'independent_whole_approval':True},{'request':ref(Path('/tmp/foundations-allocation19-eight-full-literals-independent-applied-review28-v1.json')),'whole_unit_keys':['primer-optimization.html::node-'+str(n)for n in [1552,1553,1557,1563,1566,1570,1578,1640]],'new_public_bodies':19,'independent_whole_approval':True},{'request':ref(Path('/tmp/foundations-literal-gradient15-independent-modules-full-source-review28-v1.json')),'whole_unit_keys':['primer-optimization.html::node-'+str(n)for n in [178,208,210]],'new_public_bodies':15,'independent_whole_approval':True},{'request':ref(Path('/tmp/foundations-literal-partial7-full-review28-v3/foundations-literal-partial7-full-review28-v3.json')),'whole_unit_keys':['primer-optimization.html::node-186'],'new_public_bodies':7,'independent_whole_approval':False}]
for p,h in held.items():assert sha(p)==h
j={'status':'read_only_current55_foundations_remaining_whole_unit_priority_inventory','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'current_owner':ref(ownerp),'current_inventory':ref(invp),'native_owner_counts_unchanged':f['counts'],'owned_exercise_statuses':dict(exercise),'owned_pending_exercise_count':0,'owned_partial_exercise_count':0,'pending_material_claim_records':483,'pending_material_distinct_source_units':452,'proved_material_claim_records_not_whole_unit_count':1112,'not_a_formal_claim_records':524,'families':pages,'uninstalled_future28_full_unit_work':future,'future28_independently_approved_full_literal_units':14,'future28_additional_full_literal_unit_pending_peer':1,'next_coherent_whole_unit_batch':{'unit_keys':['primer-optimization.html::node-188','primer-optimization.html::node-190'],'clauses_to_close':['Generic actual coordinate-partial entries and gradient rows; component differentiability implies full derivative.','Actual first-order little-o error and best-local-linear-map uniqueness.','Scalar-gradient row, arbitrary affine map and generic coordinatewise activation.','Literal f=(x1*x2,x1+x2^2), exact full Jacobian and value at(1,2).','Exact partial-only counterexample shows existing entries are insufficient.'],'selected_reused_source':ref(ROOT/'verification/lean/SafeLearning/CompleteFoundationsNotation.lean')},'scope':'This report counts native installed statuses and groups pending literals by their actual source headings for prioritization. It does not classify mathematical clauses from headings or mark any pending unit proved. All119 owned exercise records are complete_math; the remaining work is483 pending material claim records across452 distinct units. Fourteen full literals have independent future28 approval but remain uninstalled, and literal186 awaits its peer. Current55 source/owners/proofs are unchanged.'}
OUT.write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'pending_exercises':0,'partial_exercises':0,'pending_material_claim_records':483,'pending_distinct_units':452,'families':[{ 'source':p['source']['file'],'distinct_units':p['pending_distinct_units'],'pending_claim_records':p['pending_claim_records'],'main_heading_counts':[(g['source_heading']['text'],g['pending_distinct_units'],g['pending_claim_records'])for g in p['families_by_actual_source_h2']]}for p in pages]}))
