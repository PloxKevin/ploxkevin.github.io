#!/usr/bin/env python3
"""Check exact full-coverage ledger integrity, preserving unfinished claims.

This checks inventory/source/proof references and completion accounting. It
does not infer semantic correspondence or replace Lean compilation. Use
--require-complete only when asking whether the entire mathematical task is done.
"""
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import sys
from lean_names import declarations as source_declarations

ROOT=Path(__file__).resolve().parents[2]
CLAIM_STATUSES={'proved','definition_encoded','not_a_formal_claim','open_problem_statement','pending'}
EXERCISE_STATUSES={'complete_math','partial','pending'}
CLOSED={'proved','definition_encoded','not_a_formal_claim','open_problem_statement'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def validate():
    errors=[]
    warnings=[]
    inv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
    exercise_index={e['key']:e for e in inv['exercises']}
    material_index={u['key']:u for u in inv['material_source_units']}
    declarations={}
    proofs={}
    for path in sorted((ROOT/'verification/lean/SafeLearning').glob('*.lean')):
        if path.name=='Smoke.lean':
            continue
        text=path.read_text()
        try:
            indexed=source_declarations(text)
        except ValueError as error:
            errors.append(f'{path.name}: {error}')
            continue
        for record in indexed:
            full=record['name']
            if full in declarations:
                errors.append(f'{path.name}: duplicate local declaration {full}')
            declarations[full]=dict(file=str(path.relative_to(ROOT)),kind=record['kind'])
        proofs[str(path.relative_to(ROOT))]=digest(path)
    for source,expected in inv['source_sha256'].items():
        if digest(ROOT/source)!=expected:
            errors.append('stale inventory source: '+source)
    seen_exercises={}
    seen_material={}
    seen_pages={}
    totals=Counter()
    domains=[]
    refs=set()
    def check_claim(c,context,claimed_complete=False):
        for field in ('id','statement_in_prose','kind','status','lean_declarations',
                      'hypotheses','correspondence','remaining_gaps'):
            if field not in c:
                errors.append(f'{context}: missing claim field {field}')
        status=c.get('status')
        if status not in CLAIM_STATUSES:
            errors.append(f'{context}: unknown claim status {status}')
        totals['claim:'+str(status)]+=1
        if status in {'proved','definition_encoded'} and not c.get('lean_declarations'):
            errors.append(f'{context}: encoded/proved claim has no declaration')
        for name in c.get('lean_declarations',[]):
            refs.add(name)
            if name not in declarations:
                errors.append(f'{context}: missing local declaration {name}')
        if status!='pending' and not c.get('correspondence'):
            errors.append(f'{context}: closed claim lacks correspondence')
        if status=='pending' and not c.get('remaining_gaps'):
            errors.append(f'{context}: pending claim lacks an explicit gap')
        if claimed_complete and (status not in CLOSED or c.get('remaining_gaps')):
            errors.append(f'{context}: complete exercise contains an unresolved claim')
        for key in c.get('source_unit_keys',[]):
            if key not in material_index:
                errors.append(f'{context}: unknown material key {key}')
            seen_material.setdefault(key,[]).append(status)
    for domain in ('foundations','applied','modules','core'):
        path=ROOT/f'book/coverage/{domain}.json'
        data=json.loads(path.read_text())
        for source in data['scope_pages']:
            if source in seen_pages:
                errors.append(f'duplicate domain ownership: {source}')
            seen_pages[source]=domain
            expected=data['source_sha256'].get(source)
            if expected!=inv['source_sha256'].get(source):
                errors.append(f'{domain}: stale source fingerprint: {source}')
        for source,value in data.get('proof_files',{}).items() if isinstance(data.get('proof_files'),dict) else []:
            expected=value.get('sha256') if isinstance(value,dict) else value
            if expected and proofs.get(source)!=expected:
                errors.append(f'{domain}: stale proof fingerprint: {source}')
        if isinstance(data.get('proof_files'),list):
            for source in data['proof_files']:
                if source not in proofs:
                    errors.append(f'{domain}: missing listed proof file: {source}')
        for source,expected in data.get('proof_sha256',{}).items():
            if proofs.get(source)!=expected:
                errors.append(f'{domain}: stale separately recorded proof fingerprint: {source}')
        counts=Counter()
        for e in data['exercises']:
            key=e['inventory_key']
            if key in seen_exercises:
                errors.append('duplicate exercise: '+key)
            seen_exercises[key]=domain
            if key not in exercise_index:
                errors.append('unknown exercise: '+key)
                continue
            original=exercise_index[key]
            if e['source']!=original['source'] or e['locator']!=original['locator']:
                errors.append('wrong exercise source/locator: '+key)
            expected=e.get('text_sha256',e.get('source_text_sha256'))
            if expected and expected!=original['text_sha256']:
                errors.append('stale exercise text fingerprint: '+key)
            status=e['status']
            if status not in EXERCISE_STATUSES:
                errors.append('unknown exercise status: '+key)
            counts[status]+=1
            totals['exercise:'+status]+=1
            if not e['claims']:
                errors.append('exercise without claims: '+key)
            for c in e['claims']:
                check_claim(c,key,status=='complete_math')
        for c in data.get('material_claims',[]):
            check_claim(c,domain+':material')
        for key in data.get('pending_source_units',[]):
            if isinstance(key,dict):
                key=key.get('key',key.get('inventory_key'))
            if key not in material_index:
                errors.append(f'{domain}: unknown pending material key {key}')
            else:
                seen_material.setdefault(key,[]).append('pending')
        domains.append(dict(domain=domain,exercise_statuses=dict(counts),ledger_sha256=digest(path)))
    missing_exercises=set(exercise_index)-set(seen_exercises)
    missing_material=set(material_index)-set(seen_material)
    missing_pages=set(inv['source_sha256'])-set(seen_pages)
    if missing_exercises:
        errors.append(f'{len(missing_exercises)} exercises lack an owner')
    if missing_material:
        errors.append(f'{len(missing_material)} material source units lack a review record')
    if missing_pages:
        errors.append(f'{len(missing_pages)} pages lack an owner')
    material_status=Counter()
    for key,states in seen_material.items():
        material_status['pending' if 'pending' in states else 'reviewed']=material_status.get(
            'pending' if 'pending' in states else 'reviewed',0)+1
    complete=not errors and totals['exercise:complete_math']==len(exercise_index) and material_status['pending']==0
    return dict(schema_version=1,checked_at_utc=datetime.now(timezone.utc).isoformat(),
        integrity_status='passed' if not errors else 'failed',mathematical_coverage_complete=complete,
        inventory_sha256=digest(ROOT/'book/coverage/inventory.json'),
        counts=dict(exercises=len(exercise_index),material_source_units=len(material_index),
                    statuses=dict(totals),material_review_statuses=dict(material_status),
                    referenced_local_declarations=len(refs)),domains=domains,errors=errors,warnings=warnings,
        missing_exercises=sorted(missing_exercises),missing_material_units=sorted(missing_material),
        source_sha256=inv['source_sha256'],referenced_declarations={n:declarations[n] for n in sorted(refs) if n in declarations},
        limits=['Integrity checks do not certify semantic correspondence; that requires mathematical review.',
                'Declaration existence does not establish local compilation, kernel replay or source equivalence.',
                'Reviewed overlapping source units are not counted as independent mathematical propositions.',
                'Complete exercise rows require independent review; their number alone never establishes full material coverage.'])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'reports/full-coverage/ledger-audit.json')
    parser.add_argument('--require-complete',action='store_true')
    args=parser.parse_args()
    report=validate()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('integrity_status','mathematical_coverage_complete','counts','errors')},indent=2))
    return 0 if report['integrity_status']=='passed' and (not args.require_complete or report['mathematical_coverage_complete']) else 1

if __name__=='__main__':
    sys.exit(main())
