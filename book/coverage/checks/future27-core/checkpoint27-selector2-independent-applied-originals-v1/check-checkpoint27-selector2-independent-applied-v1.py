from pathlib import Path
import ast, collections, copy, hashlib, importlib.util, json, re, sys
ROOT=Path('/home/oxrexkevin/SafetyBased');sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
SELECTOR=ROOT/'book/coverage/prepare_checkpoint27_selection_v2.py'
ORIGINAL=ROOT/'book/coverage/prepare_checkpoint27_selection_v1.py'
RETAINER=ROOT/'book/coverage/retain_baseline_inputs27_v1.py'
OUT=Path('/tmp/checkpoint27-selector2-independent-applied-check-result-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
s=load(SELECTOR,'independent_selector27_2');r=load(RETAINER,'independent_retainer27_1')
assert sha(SELECTOR)=='1cdb720a1380e6a36aff457f2587d01123fd8455b1beed35a576dd501605efb9'
assert sha(RETAINER)=='159d6f53b2a2a05cbc68155d2925a14dc46e90b2d47392ab32c6b822877e2d33'
fixtures=[]
def accept(name,f):f();fixtures.append({'fixture':name,'result':'accepted'})
def reject(name,f):
    try:f()
    except (AssertionError,KeyError,TypeError,ValueError,FileNotFoundError):fixtures.append({'fixture':name,'result':'rejected'});return
    raise AssertionError('unexpected acceptance '+name)
for module,label in [(s,'selector'),(r,'retainer')]:
    zero=module.zero if label=='selector' else module._zero
    accept(label+' exact integer zeros',lambda z=zero:z({'actual_exit_code':0,'exit_code':0}))
    for name,body in [('boolFalse',{'actual_exit_code':False}),('float0',{'exit_code':0.0}),('missing',{}),('conflicting',{'actual_exit_code':0,'exit_code':1})]:reject(label+' '+name,lambda b=body,z=zero:z(b))
accept('strict alias command spellings agree',lambda:r._command({'actual_command':['python3','a.py'],'command':['python3','a.py']}))
reject('conflicting command aliases',lambda:r._command({'actual_command':['python3','a.py'],'command':['python3','b.py']}))
reject('missing command aliases',lambda:r._command({}))
for name in ['/tmp/execution.json','../outside.json','book//coverage/inventory.json','']:
    reject('unsafe selector path '+repr(name),lambda n=name:s.safe(n))
baseline=json.loads((ROOT/s.BASELINE).read_bytes());manifest=json.loads((ROOT/s.MANIFEST).read_bytes())
assert sha(ROOT/s.BASELINE)==s.BASELINE_SHA and sha(ROOT/s.MANIFEST)==s.MANIFEST_SHA
assert len(baseline['proof_files'])==1167 and len(manifest['frozen_inputs_sha256'])==47277
assert manifest['proof_files']==baseline['proof_files']
aliases={}
for n in r.OWNER_EVIDENCE_PATHS:
    h=manifest['working_inputs_sha256'][n]
    aliases[n]={'original_sha256':h,'immutable_byte_copy':{'file':'reports/full-coverage/owner26-originals-before-owner27-integration-v1/'+Path(n).name,'sha256':h}}
aliases[r.SOURCE]={'original_sha256':r.SOURCE_OLD_SHA,'immutable_byte_copy':{'file':r.SOURCE_ARCHIVE,'sha256':r.SOURCE_OLD_SHA}}
source_bytes=json.dumps(aliases,sort_keys=True)
assert sha(ROOT/r.SOURCE_ARCHIVE)==r.SOURCE_OLD_SHA and sha(ROOT/r.SOURCE)==r.SOURCE_NEW_SHA
sample={'sha256':'a'*64,'evidence_sha256':{n:d['original_sha256'] for n,d in aliases.items()}|{'book/coverage/checks/unchanged-fixture.json':'b'*64},'status':'historical_proved','reviewed_at_utc':'2025-01-01T00:00:00+00:00','checkpoint26_original_baseline_evidence':{'original_body':'literal body','old_exit_code':1}}
original=copy.deepcopy(sample)
normalized,used=r.normalized_baseline_evidence(sample,aliases)
assert sample==original and len(used)==5 and not set(aliases).intersection(normalized)
assert normalized['book/coverage/checks/unchanged-fixture.json']=='b'*64
fixtures.append({'fixture':'five exact original paths normalize without mutating full old row or previous provenance','result':'accepted'})
drift=copy.deepcopy(sample);drift['evidence_sha256'][r.SOURCE]='0'*64
reject('wrong historical source digest',lambda:r.normalized_baseline_evidence(drift,aliases))
reject('sixth unauthorized alias',lambda:r.normalized_baseline_evidence(sample,{**aliases,'SafeLearning/verification.html':aliases[r.SOURCE]}))
conflict=copy.deepcopy(sample);conflict['evidence_sha256'][r.SOURCE_ARCHIVE]='c'*64
reject('archive target digest conflict',lambda:r.normalized_baseline_evidence(conflict,aliases))
assert json.dumps(aliases,sort_keys=True)==source_bytes

# Exercise the exact retain() full-row gate, in isolation from future writes.
retain_ast=next(n for n in ast.parse(RETAINER.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='retain')
row_gate=next(n for n in retain_ast.body if isinstance(n,ast.For) and "baseline['proof_files'].items()" in ast.unparse(n))
fixture_source='verification/lean/SafeLearning/Fixture.lean';current={n:'d'*64 for n in aliases}
selected={fixture_source:copy.deepcopy(original)}
selected[fixture_source]['evidence_sha256']=dict(normalized)
selected[fixture_source]['checkpoint27_original_baseline_evidence']={'original_baseline_selection':r.BASELINE,'original_baseline_source':fixture_source,'original_row_canonical_json_sha256':r.canonical_row_sha256(original),'authorized_original_path_aliases':used}
selected[fixture_source]['checkpoint27_original_baseline_evidence']['original_baseline_selection']={'file':r.BASELINE,'sha256':r.BASELINE_SHA}
def row_check(rows):
    env={'baseline':{'proof_files':{fixture_source:original}},'selected':rows,'aliases':aliases,'normalized_baseline_evidence':r.normalized_baseline_evidence,'canonical_row_sha256':r.canonical_row_sha256,'baseline_name':r.BASELINE,'current_sha256':current,'sha':lambda n:r.BASELINE_SHA if n==r.BASELINE else current[n]}
    exec(compile(ast.Module(body=[copy.deepcopy(row_gate)],type_ignores=[]),'<exact-retain-fullrow-gate>','exec'),env)
accept('full old body/time and checkpoint26 provenance preserved',lambda:row_check(selected))
dual=copy.deepcopy(selected);dual[fixture_source]['evidence_sha256'][r.SOURCE]=current[r.SOURCE]
accept('authorized old archive plus exact installed current raw evidence',lambda:row_check(dual))
for name,key,value in [('old time mutation','reviewed_at_utc','now'),('old body/status mutation','status','new_proved'),('old embedded provenance mutation','checkpoint26_original_baseline_evidence',{'original_body':'rewritten'})]:
    changed=copy.deepcopy(selected);changed[fixture_source][key]=value;reject(name,lambda x=changed:row_check(x))
bad=copy.deepcopy(dual);bad[fixture_source]['evidence_sha256'][r.SOURCE]=r.SOURCE_OLD_SHA
reject('old digest resurfaced at changed raw source',lambda:row_check(bad))
bad=copy.deepcopy(dual);bad[fixture_source]['evidence_sha256'][r.SOURCE]='e'*64
reject('arbitrary new digest at changed raw source',lambda:row_check(bad))
bad=copy.deepcopy(selected);bad[fixture_source]['checkpoint27_original_baseline_evidence']['original_row_canonical_json_sha256']='f'*64
reject('wrong deterministic original full-row fingerprint',lambda:row_check(bad))

ready=json.loads((ROOT/s.PAIRS).read_bytes());assert sha(ROOT/s.PAIRS)==s.PAIRS_SHA
expected={x['canonical_source']:x['source']['sha256'] for x in ready['sources']}
all_sources=set(baseline['proof_files'])|set(expected);assert len(all_sources)==1175
parsed={}
for n in all_sources:
    text=(ROOT/n).read_text();parsed[n]=declarations(text)
    h=expected[n] if n in expected else baseline['proof_files'][n]['sha256'];assert sha(ROOT/n)==h
    for line in re.findall(r'^import[^\n]*',text,re.M):
        for dependency in line.split()[1:]:
            if dependency.startswith('SafeLearning.'):assert 'verification/lean/'+dependency.replace('.','/')+'.lean' in all_sources
new_names=[d['name'] for n in expected for d in parsed[n]]
new_theorems=[d['name'] for n in expected for d in parsed[n] if d['kind'] in {'theorem','lemma'}]
all_names=[d['name'] for n in all_sources for d in parsed[n]]
all_theorems=[d['name'] for n in all_sources for d in parsed[n] if d['kind'] in {'theorem','lemma'}]
assert len(new_names)==len(set(new_names))==201
assert len(new_theorems)==len(set(new_theorems))==141
assert len(all_names)==len(set(all_names))==12589
assert len(all_theorems)==len(set(all_theorems))==9644
fixtures.append({'fixture':'real 1175 source name and import closure with 141/9644 theorem-only counts','result':'accepted'})
assert len(new_names)!=141
decl_nodes=next(n for n in ast.parse(SELECTOR.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='prepare').body
begin=next(i for i,n in enumerate(decl_nodes) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='new_names' for t in n.targets))
end=next(i for i,n in enumerate(decl_nodes[begin:],begin) if isinstance(n,ast.For) and 'for owner in' in ast.unparse(n))
block=decl_nodes[begin:end]
cache_by_text={(ROOT/n).read_text():ds for n,ds in parsed.items()}
def declaration_count_gate(fake=None):
    env={'expected':expected,'selected':dict.fromkeys(all_sources),'safe':s.safe,'declarations':lambda text:copy.deepcopy(cache_by_text[text]) if fake is None else fake(text)}
    exec(compile(ast.Module(body=copy.deepcopy(block),type_ignores=[]),'<exact-selector27-name-gates>','exec'),env)
accept('exact source-index supporting definitions retained in closure',declaration_count_gate)
def wrong_kind(text):
    ds=copy.deepcopy(cache_by_text[text])
    for d in ds:
        if d['kind']=='def':d['kind']='theorem';break
    return ds
reject('definition miscounted as theorem',lambda:declaration_count_gate(wrong_kind))
audit=json.loads((ROOT/s.AUDIT).read_bytes());assert sha(ROOT/s.AUDIT)==s.AUDIT_SHA
assert audit['status']=='passed' and audit['proof_file_count']==1167 and audit['theorem_count']==9503
assert audit['proof_sha256']=={n:r['sha256'] for n,r in baseline['proof_files'].items()}
assert all(type(x['exit_code']) is int and x['exit_code']==0 for x in audit['checks'])
for n,row in baseline['extra_frozen_inputs'].items():assert sha(ROOT/n)==row['sha256']
assert not (ROOT/s.DESTINATION).exists() and not (ROOT/s.CONTENT_MAP).exists()
result={'status':'passed_independent_selector27_v2_full_code_and_isolated_guard_fixture_checker','errors':[],'helper':{'file':str(SELECTOR.relative_to(ROOT)),'sha256':sha(SELECTOR)},'retainer':{'file':str(RETAINER.relative_to(ROOT)),'sha256':sha(RETAINER)},'original_unexecuted_selector1':{'file':str(ORIGINAL.relative_to(ROOT)),'sha256':sha(ORIGINAL)},'original_selector1_count_blocker':{'new_public_names':201,'new_theorem_lemma_names':141,'scope':'Static/native index counterexample; selector1 was not executed.'},'fixtures':fixtures,'fixture_count':len(fixtures),'proof_source_count':1175,'baseline_source_count':1167,'new_source_count':8,'new_public_name_count':201,'new_theorem_lemma_count':141,'all_public_name_count':12589,'aggregate_theorem_lemma_count':9644,'baseline_frozen_content_bindings':47277,'baseline_extra_input_count':len(baseline['extra_frozen_inputs']),'exact_all_source_import_closure':True,'producer_or_retain_or_prepare_executed':False,'scope':'Full static/native source-index review and isolated exact guard fixtures. No installed27 integration, production plan, baseline retainer write, selection write or fresh aggregate execution is asserted.'}
with OUT.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'fixtures':len(fixtures),'all_public_names':len(all_names),'theorem_lemma':len(all_theorems),'result':str(OUT),'sha256':sha(OUT)}))
