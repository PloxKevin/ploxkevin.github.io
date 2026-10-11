"""Read-only byte/evidence guards for an independent, scoped source11.4 review."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys, traceback

ROOT=Path('/home/oxrexkevin/SafetyBased')
REQUEST=Path('/tmp/applied-lyapunov-scenario-validation23-two-source-readiness-v1.json')
REQUEST_SHA='68c7eeed2cd3a95407cc85a17c192ec4c1617fb9653cd15f34818717e4229691'
OUT=Path('/tmp/lyapunov-scenario-validation23-independent-foundations-components-review-v2.json')
FAIL=Path('/tmp/lyapunov-scenario-validation23-independent-foundations-checker-failure-v2.json')
START=datetime.now(timezone.utc).isoformat()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def path(name):
    p=Path(name)
    return p if p.is_absolute() else ROOT/p
def check_ref(row):
    p=path(row['file']);assert p.is_file() and not p.is_symlink(),str(p)
    assert sha(p)==row['sha256'],str(p)
    return p

DECISIONS={
 'genuine_binomial_probability_and_recurrence': 'The actual independent measurable equal-probability event-count law gives the binomial expression. Pascal and a finite-sum identity derive nonincrease for 0≤p≤1 and m≤n; the ten-term tail is antitone from n=9. This does not prove the optimizer support theorem.',
 'dimension_one_exact_cutoff_and_source_roundings': 'The single-term reduction and power/log iff prove the exact all-natural-number cutoff N≥135. The certified logarithm and ratio enclosures justify rounding but disprove the source chain of exact finite-decimal equalities.',
 'dimension_ten_first_crossing_with_certified_roundings': 'Exact rational 580/581 enclosures and derived antitonicity prove the first crossing at581. The proof separately handles n<9 with a nonnegative zero-count term. The printed tail decimals are certified significant-figure approximations.',
 'given_variable_count_sufficient_formula_and_comparison': 'The given decision-variable formula evaluates to10, and the given sufficient expression has ceiling861, about48% above581. The logarithmic substitution is genuine. This establishes evaluation of the supplied sufficient formula rather than a general Chernoff/scenario theorem.',
 'validation_exact_rule_and_least_integer': 'The exact corrected exponential confidence bound is equivalent to the logarithmic threshold for every natural count, with least count5757. The first-power misprint gives116. Literal rounded equality displays remain false.',
 'misprint_certified_lower_confidence_and_precision_gaps': 'The exponential Taylor enclosure proves .91137575<exp(-.0928)<.91137577 and a complement of about8.86%. That complement is the confidence lower bound furnished by this inequality, with no claim that it equals or bounds above actual procedure confidence.',
 'actual_fixed_iid_validation_population_guarantee': 'Centering actual bounded independent variables gives the MGF and sum tail used for a genuine probability≥.99 lower-mean event. Its subset gives probability≥.99 of the implication empirical≥.95 → population mean≥.93 for one fixed fresh batch. This does not establish conditional confidence given acceptance or optional repeated testing.',
 'normalized_credible_probability_to_actual_posterior_guarantee': 'The actual probability measure and credible∩stable intersection transfer normalized probability≥.93 through credible mass.95 to full stable mass≥.8835≥.88. Bernoulli laws with parameter equal to that genuine normalized probability derive the same fixed-batch accepted implication with probability≥.99. The hypotheses supply the posterior and independence; no GP construction or nonlinear stability identification is proved.'
}

def main():
    assert not OUT.exists() and not FAIL.exists()
    assert sha(REQUEST)==REQUEST_SHA
    req=read(REQUEST)
    check_ref(req['inventory'])
    inv=read(ROOT/'book/coverage/inventory.json')
    assert sha(ROOT/'book/coverage/inventory.json')==req['inventory']['sha256']
    exercises={r['key']:r for r in inv['exercises']}
    units={r['key']:r for r in inv['material_source_units']}
    literal=req['entire_inventory_record']
    assert exercises[req['exercise_key']]==literal
    assert hashlib.sha256(literal['source_text'].encode()).hexdigest()==req['exercise_text_sha256']==literal['text_sha256']
    assert sha(ROOT/literal['source'])==literal['source_sha256']
    assert len(req['material_units'])==5
    literal_rows=[]
    for row in req['material_units']:
        actual=units[row['source_unit_key']]
        assert actual==row['entire_inventory_record']
        assert hashlib.sha256(actual['source_text'].encode()).hexdigest()==actual['text_sha256']==row['unit_text_sha256']
        assert sha(ROOT/actual['source'])==actual['source_sha256']==row['source_sha256']
        literal_rows.append({'source_unit_key':row['source_unit_key'],'entire_inventory_record':actual,'whole_unit_approved':False,'retained_original_author_scope':row,'independent_scope':'Only the explicitly listed quantitative/probability components are approved; no whole-row promotion is issued by this review.'})
    source_rows=[];all_names=set();failures=[]
    for row in req['proof_rows']:
        source=check_ref(row['proof_source']);snapshot=check_ref(row['source_snapshot'])
        assert source.read_bytes()==snapshot.read_bytes()
        source_text=source.read_text()
        assert not re.search(r'\b(sorry|admit|axiom)\b',source_text)
        namespace=re.search(r'^namespace ([A-Za-z0-9_.]+)$',source_text,re.M).group(1)
        declarations=[{'name':namespace+'.'+m.group(2),'kind':m.group(1)} for m in re.finditer(r'^(theorem|lemma|def) ([A-Za-z0-9_]+)',source_text,re.M)]
        assert declarations==row['public_declarations']
        public=[d['name'] for d in declarations if d['kind'] in ('theorem','lemma')]
        all_names.update(public)
        # Preserve complete immutable source, including all proof bodies and helpers.
        actual=read(check_ref(row['actual_standalone_record']))
        assert actual==row['entire_actual_record'] and actual['actual_exit_code']==0
        assert actual['actual_command']==['lake','env','lean',actual['source_file']]
        assert actual['cwd']==str(ROOT/'verification/lean')
        assert Path(actual['source_file'])==snapshot
        assert actual['source_sha256_before']==actual['source_sha256_after']==row['proof_source']['sha256']
        assert actual['working_source_sha256_after']==row['proof_source']['sha256']
        log=check_ref(row['raw_log']);assert str(log)==actual['raw_log_file'] and sha(log)==actual['raw_log_sha256']
        runner=path(actual['runner_file']);assert sha(runner)==actual['runner_sha256']
        assert 'subprocess.run' in runner.read_text()
        assert log.stat().st_size>0 and 'error:' not in log.read_text()
        for old in row['historical_failed_trials']:
            rec=read(check_ref(old['record']));assert rec==old['entire_original_record'] and rec['actual_exit_code']==1
            snap=check_ref(old['source_snapshot']);old_log=check_ref(old['raw_log'])
            assert str(snap)==rec['source_file'] and sha(snap)==rec['source_sha256_before']==rec['source_sha256_after']
            assert str(old_log)==rec['raw_log_file'] and sha(old_log)==rec['raw_log_sha256']
            assert rec['actual_command']==['lake','env','lean',str(snap)] and rec['cwd']==str(ROOT/'verification/lean')
            assert sha(path(rec['runner_file']))==rec['runner_sha256']
            assert re.search(r'\berror(?:\(|:)',old_log.read_text())
            failures.append(old)
        source_rows.append({'proof_source':row['proof_source'],'entire_source_and_all_proof_bodies':source_text,'public_theorem_names':public,'actual_original_standalone_record':row['actual_standalone_record'],'entire_actual_original_record':actual,'raw_log':row['raw_log'],'raw_log_nonempty_warning_bytes_preserved':True,'source_snapshot':row['source_snapshot'],'runner':{'file':str(runner),'sha256':sha(runner)},'compiler_scope':'Actual immutable TMP standalone source only; no new canonical, named or aggregate execution.'})
    assert len(all_names)==req['theorem_count']==25 and len(failures)==5
    assert len(req['approved_by_author_components'])==8
    assert {r['id'] for r in req['approved_by_author_components']}==set(DECISIONS)
    components=[]
    referenced=set()
    for old in req['approved_by_author_components']:
        assert set(old['lean_declarations'])<=all_names
        referenced.update(old['lean_declarations'])
        components.append({'id':old['id'],'status':'approved_complete_precise_quantitative_component','approved':True,'lean_declarations':old['lean_declarations'],'original_author_component_unchanged':old,'independent_reason':DECISIONS[old['id']],'whole_exercise_or_material_unit_approval':False})
    assert referenced==all_names
    manifest_path=ROOT/req['protected_selected_sources']['manifest']
    assert sha(manifest_path)==req['protected_selected_sources']['manifest_sha256']
    manifest=read(manifest_path);assert len(manifest['proof_files'])==1089
    for name,row in manifest['proof_files'].items():assert sha(ROOT/name)==row['sha256'],name
    dependency_rows=[]
    for row in req['selected21_dependency_rows']:
        assert sha(ROOT/row['source_file'])==row['sha256']==manifest['proof_files'][row['source_file']]['sha256']
        assert row['retained_selected21_row']==manifest['proof_files'][row['source_file']]
        for evidence in row['existing_evidence']:check_ref(evidence)
        dependency_rows.append(row)
    assert len(dependency_rows)==6
    for primary in req['primary_source_correspondence']:
        assert sha(ROOT/primary['source_file'])==primary['sha256']
    frozen22=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
    for name,row in frozen22['proof_files'].items():assert sha(ROOT/name)==row['sha256']
    for name,digest in frozen22['working_inputs_sha256'].items():
        if name.startswith('SafeLearning/') or name in {'book/coverage/inventory.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/core.json'}:assert sha(ROOT/name)==digest
    reader_history=[]
    for name in ['review-lyapunov-scenario-validation23-independent-foundations-v1.py','lyapunov-scenario-validation23-independent-foundations-checker-failure-v1.json','lyapunov-scenario-validation23-independent-foundations-execution-v1.json','lyapunov-scenario-validation23-independent-foundations-execution-v1.log']:
        p=Path('/tmp')/name
        reader_history.append({'file':str(p),'sha256':sha(p)})
    assert read(Path('/tmp/lyapunov-scenario-validation23-independent-foundations-execution-v1.json'))['actual_exit_code']==1
    report={'status':'passed_independent_quantitative_source11_4_components_review_future23','reviewed_by':'/root/config21_next','started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':{'file':str(REQUEST),'sha256':REQUEST_SHA},'original_request_created_at_utc':req['created_at_utc'],'actual_checker':str(Path(__file__)),'actual_checker_sha256':sha(Path(__file__)),'errors':[],'preserved_original_checker_failure_history':reader_history,'original_checker_failure_reason':'Reader v1 accepted only error: diagnostics; genuine Lean error(lean.unknownIdentifier): also denotes an error. New v2 accepts both without changing source/trial/semantic decisions.','exercise_key':req['exercise_key'],'entire_current48_exercise_literal_record':literal,'component_decisions':components,'physical_literal_rows':literal_rows,'full_source_proof_reviews':source_rows,'all_five_original_failed_trials_exact':failures,'selected21_dependencies_exact':dependency_rows,'primary_scoped_sources':req['primary_source_correspondence'],'all1089_selected21_and1113_selected22_sources_exact':True,'all_current48_assets_inventory_and_four_working22_ledgers_exact':True,'public_theorem_count':25,'whole_exercise_approved':False,'whole_material_unit_promotions':[],'coverage_complete':False,'limits':['The source(a)/(c) rounded finite-decimal equality displays are literally false and remain source gaps, despite certified corrected numerical conclusions.','The independent Bernoulli count identity does not prove the general Campi–Garatti scenario optimizer theorem or its support/missed-region interpretation.','The posterior validation theorem proves probability≥.99 of an accepted fixed-batch implication, not conditional probability≥.99 given acceptance, optional repeated-until-pass testing, GP posterior construction, or nonlinear stability.','The credible posterior and actual Bernoulli parameter equality and independence are explicit mathematical hypotheses rather than inferred from an implementation.','Both original runners create source snapshots before compilation but serialize the fields called source_sha256_before/after after compilation. This review binds immutable snapshots and exact original record fields without inventing a separately observed pre-execution hash capture.','Only TMP review/checker files are written. Named/canonical compiler runs, aggregate23 audit, exercise coverage mapping and publication remain separate.']}
    with OUT.open('x') as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'review':str(OUT),'review_sha256':sha(OUT),'theorems':25,'components':8,'whole_exercise_approved':False}))

if __name__=='__main__':
    try:main()
    except Exception:
        failure=traceback.format_exc()
        if not FAIL.exists():
            with FAIL.open('x') as f:f.write(json.dumps({'status':'failed','started_at_utc':START,'failed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':str(Path(__file__)),'checker_sha256':sha(Path(__file__)),'failure':failure},indent=2)+'\n')
        sys.stderr.write(failure);sys.exit(1)
