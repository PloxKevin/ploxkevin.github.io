from pathlib import Path
from datetime import datetime, timezone
from html.parser import HTMLParser
import hashlib, importlib.util, json, re, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = ROOT / 'book/coverage/checks/future31-applied/growth10-whole-independent-v1'
REQUEST = Path('/tmp/foundations-growth10-current1271-full-review31-v1/foundations-growth10-logdet-Taylor-full-source-entire-current1271-whole-independent-review-request31-v1.json')
REQUEST_SHA = 'b2af52fd095e1f6ff92adf1688fc630f86d47247fa582b8d828951ab773126aa'
SOURCE = Path('/tmp/CompleteFoundationsGrowthExamplesLogDetTaylor31-draft-v3.lean')
SOURCE_SHA = '15f77c10cb8a419bead3441f9471f823e32b4062194a5627989338afd5a336a9'
CONTEXT = Path('/tmp/root_tmp_lean_current81_historical_owner30_context_v1.json')
CONTEXT_SHA = 'f9490760c85e8be1392f271bdf65e193e5a5e4cfc2ba29b5f7e4d32c682a7af9'
MANUAL = Path('/tmp/applied-finish31-growth10-manual-assessment-v1.json')

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def descriptor(p):
    p = Path(p)
    return {'file':str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
            'sha256':sha(p),'bytes':p.stat().st_size}

start = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
assert not OUT.exists()
assert sha(REQUEST) == REQUEST_SHA and sha(SOURCE) == SOURCE_SHA and sha(CONTEXT) == CONTEXT_SHA
d = json.loads(REQUEST.read_bytes())
manual = json.loads(MANUAL.read_bytes())
context = json.loads(CONTEXT.read_bytes())
assert context['status'] == 'actual_source81_with_unchanged_raw_source79_owner30_for_tmp_trials_only'
OUT.mkdir(parents=True)
aliases = {}
required = {}
reused = {
    d['current_inventory']['sha256']:Path(d['current_inventory']['file']),
    d['current_installed30_foundations_owner']['sha256']:Path(d['current_installed30_foundations_owner']['file'])
}

def retain(p, expected=None):
    p = Path(p)
    assert p.is_file() and not p.is_symlink()
    h = sha(p)
    if expected is not None:
        assert h == expected, str(p)
    if h in reused:
        target = reused[h]
        assert sha(target) == h
    else:
        target = OUT / 'original-byte-aliases' / h / p.name
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            with target.open('xb') as f:
                f.write(p.read_bytes())
        assert sha(target) == h
    z = descriptor(target)
    aliases[str(p)] = z
    required[z['file']] = h
    return z

request = retain(REQUEST, REQUEST_SHA)
source = retain(SOURCE, SOURCE_SHA)
manual_file = retain(MANUAL)
helper = retain(Path(__file__))
for p,h in d['all_physical_original_inputs_sha256'].items():
    retain(p,h)
for logical,z in d['all_original_byte_aliases'].items():
    aliases[logical] = retain(z['file'],z['sha256'])
    assert aliases[logical]['bytes'] == z['bytes']
extra_primary = retain(ROOT/'verification/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean')
names_path = ROOT/'book/coverage/lean_names.py'
retain(names_path)
spec=importlib.util.spec_from_file_location('growth_review_names',names_path)
names=importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
for p in [SOURCE, *[Path(z['file']) for z in d['entire_complete_selected_dependencies']]]:
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b',names.without_comments(p.read_text()))

class Page(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.paragraphs=[]
        self.parts=None
        self.ids=[]
    def handle_starttag(self,t,a):
        self.ids.extend(v for k,v in a if k=='id')
        if t=='p':
            assert self.parts is None
            self.parts=[]
    def handle_endtag(self,t):
        if t=='p':
            assert self.parts is not None
            self.paragraphs.append(''.join(self.parts))
            self.parts=None
    def handle_data(self,t):
        if self.parts is not None:self.parts.append(t)

norm=lambda s:' '.join(s.split())
literal=d['entire_current_literal']
assert hashlib.sha256(literal['source_text'].encode()).hexdigest()==literal['text_sha256']
original_page=Path(d['current_source']['file'])
original_parser=Page();original_parser.feed(original_page.read_text());original_parser.close()
assert sum(norm(p)==norm(literal['source_text']) for p in original_parser.paragraphs)==1
actual_page=ROOT/'SafeLearning/primer-basics.html'
assert sha(actual_page)==context['held_current_source_sha256']['SafeLearning/primer-basics.html']
actual_parser=Page();actual_parser.feed(actual_page.read_text());actual_parser.close()
assert sum(norm(p)==norm(literal['source_text']) for p in actual_parser.paragraphs)==1
actual_page_retained=retain(actual_page)
linked=[]
for k,z in d['complete_local_linked_target_pages'].items():
    p=Path(z['file']);parser=Page();parser.feed(p.read_text());parser.close()
    anchor='training-with-lipsdp' if k.endswith('lipsdp.html') else 'lagrangian-duality'
    assert parser.ids.count(anchor)==1
    if anchor=='training-with-lipsdp':
        assert any('symmetric perturbation' in text and r'N\succ0' in text for text in parser.paragraphs)
        assert r'\log\det(N+\varepsilon E)=\log\det N+\varepsilon\,\mathrm{tr}(N^{-1}E)+O(\varepsilon^2)' in p.read_text()
    else:
        assert any(r'C\eta' in text and r'independent of $\eta$' in text for text in parser.paragraphs)
    linked.append({'local_page':k,'full_exact_source':retain(p,z['sha256']),
        'entire_file_parsed':True,'target_anchor':anchor,'target_anchor_unique':True,
        'relevant_full_target_and_domain_context_read':True,'unrelated_whole_page_approval':False})

def native(record):
    n=json.loads(Path(record).read_bytes())
    assert n['status']=='passed_actual_tmp_lean_only' and n['actual_exit_code']==0
    assert n['actual_runner_exit_code']==0 and n['protection_errors']==[]
    assert n['source_sha256_before']==n['source_sha256_after']==n['source_snapshot_sha256']
    assert n['actual_source81_historical_source79_owner30_context']['sha256']==CONTEXT_SHA
    for key in ['original_actual_runner','actual_source81_historical_source79_owner30_context']:
        retain(n[key]['file'],n[key]['sha256'])
    source=retain(n['source'],n['source_sha256_before'])
    snapshot=retain(n['source_snapshot'],n['source_snapshot_sha256'])
    log=retain(n['raw_log'],n['raw_log_sha256'])
    return {'native':retain(record),'source':source,'snapshot':snapshot,'raw_log':log,
        'actual_exit_code':0,'original_body_times':{k:n[k]for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},
        'actual_warning_headers':len(re.findall(r'(?m)^.*: warning:',Path(n['raw_log']).read_text()))}

fresh=native('/tmp/applied-finish31-growth10-Source81-fresh-native-v1.json')
axiom=native('/tmp/applied-finish31-growth10-Source81-axiom-native-v1.json')
assert fresh['source']['sha256']==SOURCE_SHA and fresh['raw_log']['bytes']==0
assert fresh['actual_warning_headers']==axiom['actual_warning_headers']==0
assert Path('/tmp/applied-finish31-growth10-axiom-inspection-v1.lean').read_bytes().startswith(SOURCE.read_bytes())
axiom_log=Path('/tmp/applied-finish31-growth10-Source81-axiom-native-v1.log').read_text()
printed=re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]+)\]",axiom_log,re.M)
qualified=['SafeLearning.CompleteFoundationsGrowthExamplesLogDetTaylor31.'+n for n in d['public_theorem_names']]
assert [n for n,_ in printed]==qualified
assert all(set(re.split(r',\s*',a))=={'propext','Classical.choice','Quot.sound'}for _,a in printed)
histories=[]
for entry in d['genuine_original_compiler_histories']:
    n=json.loads(Path(entry['native']['file']).read_bytes())
    assert n['actual_exit_code']==entry['actual_exit_code']
    for k in ['started_at_utc','finished_at_utc','elapsed_seconds']:assert n[k]==entry[k]
    row=dict(entry)
    for k in ['native','source','snapshot','raw_log']:
        z=entry[k];row[k]=retain(z['file'],z['sha256']);assert row[k]['bytes']==z['bytes']
    assert len(re.findall(r'(?m)^.*: warning:',Path(entry['raw_log']['file']).read_text()))==entry['emitted_diagnostic_warning_headers']
    histories.append(row)

s=SOURCE.read_text();theorems=list(re.finditer(r'^theorem\s+(\w+)\s*',s,re.M))
assert len(theorems)==len(manual['public_theorem_assessments_in_source_order'])==10
reviewed=[]
for i,m in enumerate(theorems):
    assert m.group(1)==d['public_theorem_names'][i]
    tail=s[m.start():];stop=re.search(r'(?m)^(?:theorem|end |namespace |section |variable )',tail[1:]);body=tail[:stop.start()+1]if stop else tail
    reviewed.append({'declaration':qualified[i],'actual_signature':body.split(':= by',1)[0].strip(),
        'line':s[:m.start()].count('\n')+1,'exact_source_block_sha256':hashlib.sha256(body.encode()).hexdigest(),
        'entire_body_read':True,'assessment':manual['public_theorem_assessments_in_source_order'][i],
        'axioms':['propext','Classical.choice','Quot.sound']})

report={'status':'passed_independent_Growth10_full_source_entire_exact_current1271_review_with_actual_Source81_native',
    'errors':[],'reviewer':manual['reviewer'],'request':request,'entire_source':source,
    'public_theorem_count':10,'entire_ten_body_assessments':reviewed,'manual_assessment':manual_file,
    'entire_exact_literal':literal,'entire_node_decision':manual['entire_node_decision'],
    'actual_Source81_literal_identity':{'current_page':actual_page_retained,'exact_requested_literal_text_sha256':literal['text_sha256'],
        'full_current_context_in_request_manually_read':True,'actual_independent_paragraph_parser_exact_match':True},
    'complete_selected_dependencies':[aliases[z['file']]for z in d['entire_complete_selected_dependencies']],
    'complete_used_primary_files':{k:aliases[z['file']]for k,z in d['complete_used_primary_files'].items()},
    'additional_complete_primary_LinearAlgebra_Matrix_PosDef':extra_primary,
    'selected_dependency_assessment':manual['selected_dependency_assessment'],
    'primary_body_assessment':manual['primary_body_assessment'],'complete_linked_local_source_pages':linked,
    'full_exact_referenced_target_contexts':d['full_exact_referenced_target_contexts'],
    'linked_source_assessment':manual['linked_source_assessment'],'scope_boundaries':manual['scope_boundaries'],
    'all_three_genuine_author_compiler_histories':histories,
    'actual_fresh_exact_source_Source81_native':fresh,'actual_separate_all10_axiom_Source81_native':axiom,
    'historical_author_Source79_native_labels_or_body_times_rewritten':False,
    'actual_new_Source81_context':aliases[str(CONTEXT)],
    'actual_raw_owner_context':'unchanged historical Source79 owner30; ownership rebase and aggregate Source81 verification remain separate',
    'raw_owner_or_canonical_selection_or_publication_mutation':False,'whole_neighbor_or_linked_page_promotion':False,
    'coverage_complete':False,'no_recursive_prior_provenance_or_lake_build_cache_copy':True,
    'actual_static_finalizer_execution':{'command':['python3',str(Path(__file__))],'helper':helper,
        'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,
        'actual_exit_code':0,'additional_compiler_or_old_Source79_guard_invoked':False},
    'full_file_original_byte_aliases':aliases,'required_evidence_artifacts_sha256':required}
p=OUT/'growth10-entire-current1271-independent-applied31-peer-v1.json'
with p.open('x')as f:f.write(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'peer':descriptor(p),'full_file_aliases':len(aliases)}))
