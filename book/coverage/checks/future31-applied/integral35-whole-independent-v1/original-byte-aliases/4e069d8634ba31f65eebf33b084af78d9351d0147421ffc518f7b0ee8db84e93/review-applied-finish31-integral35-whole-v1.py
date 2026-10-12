from pathlib import Path
from datetime import datetime, timezone
from html.parser import HTMLParser
import hashlib, importlib.util, json, re, subprocess, time

ROOT = Path('/home/oxrexkevin/SafetyBased')
OUT = ROOT / 'book/coverage/checks/future31-applied/integral35-whole-independent-v1'
REQUEST = Path('/tmp/modules-integral-tracking35-full-current-prospective31-v1/modules-integral-tracking35-full-current-prospective-Exercise14_5-four-literals-review-request31-v3.json')
REQUEST_SHA = 'd3eff62374b65a09c5f6410a8925da268332f0e07fde7f5194e3ed9e983e5f5e'
SOURCE = Path('/tmp/CompleteModulesIntegralTrackingWhole30-draft-v15.lean')
SOURCE_SHA = '384484a7fb9d48fcb00c76a52b004ae3bbf3697b4acc71b14c9f7c0f0f17fc9a'
CONTEXT = Path('/tmp/root_tmp_lean_current79_owner30_finalcss_context_v1.json')
CONTEXT_SHA = '73ab502d42458069b9c5a9cfaa9a501c588558493eba0ea635b0a1eb869e6e72'
MANUAL = Path('/tmp/applied-finish31-integral35-manual-assessment-v1.json')

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def descriptor(p):
    p = Path(p)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
            'sha256': sha(p), 'bytes': p.stat().st_size}

started = datetime.now(timezone.utc).isoformat()
tick = time.monotonic()
assert not OUT.exists()
assert sha(REQUEST) == REQUEST_SHA and sha(SOURCE) == SOURCE_SHA
assert sha(CONTEXT) == CONTEXT_SHA
d = json.loads(REQUEST.read_bytes())
context = json.loads(CONTEXT.read_bytes())
manual = json.loads(MANUAL.read_bytes())

process_output = subprocess.run(['ps', '-eo', 'pid,ppid,etimes,stat,comm,args'],
                                check=True, text=True, capture_output=True).stdout
processes = [line for line in process_output.splitlines()
             if re.search(r'\s(?:lean|lake)\s', line) or 'root_tmp_lean_current' in line]
OUT.mkdir(parents=True)
aliases = {}
required = {}
reused = {
    '6f347b3d512a5ce36222e72e8236eb350f3218ace430c3a9dabd8776a03fbc34': ROOT / 'book/coverage/checks/modules-future30/current79-three-fragments-final-v1/modules30-current79-real30-three-fragments-candidate-v1.json',
    '9f2a37c42e8a54b81ea542ead730dbfa1d3f665be469c41e4eaa6a27703520de': ROOT / 'book/coverage/inventory-after-correction79.json'
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

request_retained = retain(REQUEST, REQUEST_SHA)
source_retained = retain(SOURCE, SOURCE_SHA)
manual_retained = retain(MANUAL)
helper_retained = retain(Path(__file__))
for p, h in d['all_physical_original_inputs_sha256'].items():
    retain(p, h)
for logical, physical in d['all_original_byte_aliases'].items():
    z = retain(physical['file'], physical['sha256'])
    assert z['bytes'] == physical['bytes']
    aliases[logical] = z

for key in ['actual_author_preparation', 'author_preparation_wrapper', 'current_context', 'narrow_independent_peer']:
    z = d[key]
    retain(z['file'], z['sha256'])
for p, z in d['actual_author_preparation_original_byte_aliases'].items():
    aliases[p] = retain(z['file'], z['sha256'])

additional_primary = []
for n in ['Analysis/Calculus/MeanValue.lean', 'Analysis/Calculus/ContDiff/Basic.lean']:
    p = ROOT / 'verification/lean/.lake/packages/mathlib/Mathlib' / n
    additional_primary.append({'module_relative_file': n, 'exact_complete_source_text': retain(p)})
names_file = ROOT / 'book/coverage/lean_names.py'
names_retained = retain(names_file)
spec = importlib.util.spec_from_file_location('review_names', names_file)
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
for z in [source_retained, *[aliases[v['file']] for v in d['complete_selected_sources'].values()]]:
    s = names.without_comments((ROOT / z['file']).read_text())
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_elab|ofReduceBool|sorryAx)\b', s)

class Paragraphs(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = None
        self.paragraphs = []
    def handle_starttag(self, tag, attrs):
        if tag == 'p':
            assert self.parts is None
            self.parts = []
    def handle_endtag(self, tag):
        if tag == 'p':
            assert self.parts is not None
            self.paragraphs.append(''.join(self.parts))
            self.parts = None
    def handle_data(self, data):
        if self.parts is not None:
            self.parts.append(data)

norm = lambda s: ' '.join(s.split())
current = Path(d['current_page_immutable_original']['file']).read_text()
proposed = Path(d['prospective_page']['file']).read_text()
assert sha(d['current_page_immutable_original']['file']) == d['current_page_immutable_original']['sha256']
replacements = [
    (r'\xi=-0.833', r'\xi=-5/6\approx-0.833'),
    ('spectral radius $0.632$ ($b=1$)', r'spectral radius $\sqrt{2/5}\approx0.632$ ($b=1$)'),
    ('and $0.616$ ($b=1.2$)', r'and $\sqrt{19/50}\approx0.616$ ($b=1.2$)')
]
transformed = current
for a, b in replacements:
    assert transformed.count(a) == 1
    transformed = transformed.replace(a, b)
assert transformed == proposed
parsers = []
for text in [current, proposed]:
    parser = Paragraphs()
    parser.feed(text)
    parser.close()
    parsers.append(parser)
for literal in d['entire_current_material_literals']:
    sha_text = hashlib.sha256(literal['source_text'].encode()).hexdigest()
    assert sha_text == literal['text_sha256']
    assert sum(norm(p) == norm(literal['source_text']) for p in parsers[0].paragraphs) == 1
prospective_literal = d['entire_prospective_exercise_and_changed_material']['nn-in-the-loop.html::node-1247']['entire_proposed']
assert sum(norm(p) == norm(prospective_literal['source_text']) for p in parsers[1].paragraphs) == 1
for literal in d['entire_current_material_literals']:
    if literal['key'] != 'nn-in-the-loop.html::node-1247':
        assert sum(norm(p) == norm(literal['source_text']) for p in parsers[1].paragraphs) == 1

def native(record, passed):
    record = Path(record)
    n = json.loads(record.read_bytes())
    z = retain(record)
    assert (n['status'] == 'passed_actual_tmp_lean_only') == passed
    assert n['actual_exit_code'] == (0 if passed else 1)
    assert n['protection_errors'] == []
    assert n['source_sha256_before'] == n['source_sha256_after'] == n['source_snapshot_sha256']
    source = retain(n['source'], n['source_sha256_before'])
    snapshot = retain(n['source_snapshot'], n['source_snapshot_sha256'])
    log = retain(n['raw_log'], n['raw_log_sha256'])
    for key in ['original_actual_runner', 'actual_source79_final_css_owner30_context']:
        if key in n:
            retain(n[key]['file'], n[key]['sha256'])
    return {'native': z, 'source': source, 'snapshot': snapshot, 'raw_log': log,
            'actual_exit_code': n['actual_exit_code'],
            'original_body_times': {k:n[k] for k in ['started_at_utc','finished_at_utc','elapsed_seconds']},
            'actual_warning_headers': len(re.findall(r'(?m)^.*: warning:', Path(n['raw_log']).read_text()))}

histories = []
for history in d['all12_genuine_compiler_histories']:
    actual = json.loads(Path(history['native']['file']).read_bytes())
    for key in ['native','source','snapshot','raw_log']:
        z = history[key]
        assert sha(z['file']) == z['sha256'] and Path(z['file']).stat().st_size == z['bytes']
    assert actual['actual_exit_code'] == history['actual_exit_code']
    assert {k:actual[k] for k in history['original_body_times']} == history['original_body_times']
    assert len(re.findall(r'(?m)^.*: warning:',Path(history['raw_log']['file']).read_text())) == history['actual_emitted_warning_headers']
    remapped = dict(history)
    for key in ['native','source','snapshot','raw_log']:
        remapped[key] = retain(history[key]['file'], history[key]['sha256'])
    histories.append(remapped)
    for key in ['source','source_snapshot','raw_log']:
        path = actual[key]
        physical_key = {'source':'source','source_snapshot':'snapshot','raw_log':'raw_log'}[key]
        aliases[path] = remapped[physical_key]
    for key in ['original_actual_runner', 'actual_source79_final_css_owner30_context', 'actual_source77_owner29_context']:
        if key in actual and Path(actual[key]['file']).is_file():
            retain(actual[key]['file'], actual[key]['sha256'])

fresh = native('/tmp/applied-finish31-integral35-fresh-native-v1.json', True)
assert fresh['source']['sha256'] == SOURCE_SHA
axiom = native('/tmp/applied-finish31-integral35-axiom-native-v1.json', True)
base = SOURCE.read_bytes()
assert Path('/tmp/applied-finish31-integral35-axiom-inspection-v1.lean').read_bytes().startswith(base)
axiom_text = Path('/tmp/applied-finish31-integral35-axiom-native-v1.log').read_text()
matches = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]+)\]", axiom_text, re.M)
assert [name for name, _ in matches] == d['full35_public_theorem_names']
assert all(set(re.split(r',\s*', axioms)) == {'propext','Classical.choice','Quot.sound'} for _, axioms in matches)
failed_extra = native('/tmp/applied-finish31-integral35-correspondence-native-v1.json', False)
passed_extra = native('/tmp/applied-finish31-integral35-correspondence-native-v2.json', True)
assert Path('/tmp/applied-finish31-integral35-correspondence-v2.lean').read_bytes().startswith(base)
extra_text = Path('/tmp/applied-finish31-integral35-correspondence-native-v2.log').read_text()
extra_matches = re.findall(r"^'([^']+)' depends on axioms:\s*\[([^]]+)\]", extra_text, re.M)
assert len(extra_matches) == 4
assert all(set(re.split(r',\s*', axioms)) == {'propext','Classical.choice','Quot.sound'} for _, axioms in extra_matches)

source_text = SOURCE.read_text()
public = list(re.finditer(r'^theorem\s+(\w+)\s*', source_text, re.M))
assert len(public) == 35 and len(manual['reviewed_public_theorem_assessments_in_request_order']) == 35
reviewed = []
for i, match in enumerate(public):
    name = 'SafeLearning.CompleteModulesIntegralTrackingWhole30.' + match.group(1)
    assert name == d['full35_public_theorem_names'][i]
    tail = source_text[match.start():]
    stop = re.search(r'(?m)^(?:theorem|private theorem|def|end |namespace )', tail[1:])
    body = tail[:stop.start()+1] if stop else tail
    signature = body.split(':= by', 1)[0].strip()
    reviewed.append({'declaration': name, 'line': source_text[:match.start()].count('\n')+1,
                     'actual_signature': signature, 'exact_source_block_sha256': hashlib.sha256(body.encode()).hexdigest(),
                     'entire_body_read': True, 'manual_assessment': manual['reviewed_public_theorem_assessments_in_request_order'][i],
                     'fresh_native_full_source_passed': True, 'axioms': ['propext','Classical.choice','Quot.sound']})

finished = datetime.now(timezone.utc).isoformat()
report = {
    'status': 'passed_independent_integral35_entire_source_Source79_three_literals_and_prospective_entire_Exercise14_5_review',
    'errors': [], 'reviewer': manual['reviewer'], 'request': request_retained,
    'entire_source': source_retained, 'manual_assessment': manual_retained,
    'all35_public_proof_body_assessments': reviewed,
    'private_bodies': manual['private_body_assessments'],
    'whole_literal_decisions': manual['whole_literal_decisions'],
    'scope_boundaries': manual['scope_boundaries'],
    'full_current_literals': d['entire_current_material_literals'],
    'entire_current_exercise': d['entire_current_exercise'],
    'entire_prospective_exercise_and_changed_literal': d['entire_prospective_exercise_and_changed_material'],
    'actual_independent_paragraph_parser': {'current_and_prospective_four_literals_match_exact_text': True,
        'exact_three_phrase_page_transformation': True, 'tag_attribute_or_other_source_change': False},
    'complete_selected_six_sources': {k: aliases[v['file']] for k,v in d['complete_selected_sources'].items()},
    'complete_used_primary_files': {k: aliases[v['file']] for k,v in d['complete_used_primary_files'].items()},
    'additional_complete_direct_primary_sources': additional_primary,
    'used_primary_body_assessment': manual['used_primary_assessment'],
    'primary_Pauli_attribution_scope': manual['primary_attribution'],
    'author_all12_genuine_histories_preserved': histories,
    'fresh_guarded_exact_source_native': fresh, 'separate_actual_all35_axiom_native': axiom,
    'separate_supplemental_correspondence_native_histories': [failed_extra, passed_extra],
    'supplemental_successful_declarations': [name for name,_ in extra_matches],
    'failed_supplemental_trial_scope': 'Syntax/type failure only in the added derivative binding; its emitted sorryAx is retained and never treated as successful native evidence. Exact v15 source passed separately.',
    'original_native_JSON_body_times_paths_and_failures_rewritten': False,
    'before_static_historical_closure_actual_running_lean_lake_or_context_processes': processes,
    'historical_Source79_finalCSS_owner30_context_used_by_actual_fresh_natives': aliases[str(CONTEXT)],
    'contextual_guard_protected_selected_sources': 1242,
    'contextual_guard_current_assets': 31, 'contextual_guard_raw_owner_files': 5,
    'current_owner_or_inventory_components_promoted_to_whole_by_copy': False,
    'narrow_peer_scope_is_separate': True, 'narrow_peer': aliases[d['narrow_independent_peer']['file']],
    'canonical_owner_selection_or_publication_mutations': False, 'coverage_complete': False,
    'actual_review_execution': {'command': ['python3', str(Path(__file__))],
        'started_at_utc': started, 'finished_at_utc': finished, 'elapsed_seconds': time.monotonic()-tick,
        'actual_helper': helper_retained, 'actual_exit_code': 0,
        'historical_exact_source_and_native_before_after_guard_records_verified': True,
        'current_source_or_owner_guard_invoked_by_static_finalizer': False,
        'native_original_Source79_context_relabelled_as_later_current_context': False},
    'no_recursive_older_snapshot_or_lake_build_cache_copy': True,
    'full_file_original_byte_aliases': aliases,
    'required_evidence_artifacts_sha256': required
}
target = OUT / 'integral35-entire-current-prospective-independent-applied31-peer-v1.json'
with target.open('x') as f:
    f.write(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
print(json.dumps({'status':report['status'],'peer':descriptor(target),
                  'retained_alias_count':len(aliases),'new_package_files':len(list(OUT.rglob('*'))),
                  'current_whole_exercise':False,'prospective_whole_exercise':True}))
