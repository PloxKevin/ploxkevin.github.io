"""Read-only identity checks for the exact current module ledger inputs.

Old review inventory labels and semantic decisions remain historical. This checks
current mapped physical units and every explicit prior reference without editing
or promoting a semantic review.
"""
import hashlib
import json
from pathlib import Path


def check_bindings(root, ledger, inventory):
    def digest(path):
        return hashlib.sha256((root/path).read_bytes()).hexdigest()

    immutable='book/coverage/inventory-after-correction31.json'
    expected='66417d2bcf2a2ee3a3eb669b657f895ac138d357c65c4f22697c3d29dbfa1661'
    assert digest(immutable)==digest('book/coverage/inventory.json')==expected
    assert inventory==json.loads((root/immutable).read_text())
    historical_inventory='book/coverage/inventory-after-correction30.json'
    historical_inventory_sha='9543b1c9320f348de8365574bbb04901fa140569618d322f66fa4cb45073e523'
    assert digest(historical_inventory)==historical_inventory_sha
    historical=json.loads((root/historical_inventory).read_text())
    unchanged_owned={}
    for section in ('exercises','material_source_units'):
        before={row['key']:row for row in historical[section] if row['source'] in ledger['scope_pages']}
        after={row['key']:row for row in inventory[section] if row['source'] in ledger['scope_pages']}
        assert before==after,(section,'Module-owned source records changed across correction31')
        unchanged_owned[section]=len(after)
    history_path='reports/full-coverage/module-history/inventory31-binding-20261010/preserved-history.json'
    history_sha='f8ec1920d2a35ada4bb46dfee9034e7cdd8337894c80e2e6fa415e72f29c9ea4'
    assert digest(history_path)==history_sha
    for saved in json.loads((root/history_path).read_text())['records']:
        assert digest(saved['preserved'])==saved['sha256']
    prior_guard='book/coverage/checks/modules-source-current-bindings18-current.json'
    prior_guard_sha='9415373652e5a756ae68b2faccc04bec2cd91b0b9e9dab089b0be24b7e1abe0c'
    assert digest(prior_guard)==prior_guard_sha
    external_checks=[
        ('book/coverage/checks/correction31-independent-root-postwrite-integrity.json','61ac9917ef37d1636ad45a4aef7b75b0d6c8cf1326005c3bfd05e7def93db31f','independent_current_source_inventory_history_and_rebase_integrity_passed'),
        ('book/coverage/checks/foundations-correction31-independent-applied-source-rebase-confirmation-v1.json','cabd29e88e5255a7a1472566bbb10c941075fb513f46071e07402c97a59921ed','independent_exact_correction31_source_and_unchanged_review_rebases_confirmed')]
    for path,expected_sha,expected_status in external_checks:
        assert digest(path)==expected_sha
        check=json.loads((root/path).read_text())
        assert check['status']==expected_status and not check.get('missing_clauses',[])
    final_path='book/coverage/checks/foundations-correction31-ledger-integrity-final.json'
    final_sha='48ed0a0f3039e6ecb84e537b6d1d4f25455b9e8db21875499a01ed52b685a072'
    assert digest(final_path)==final_sha
    final=json.loads((root/final_path).read_text());assert final['integrity_status']=='passed' and not final['errors']
    inventory_rebase=dict(previous_inventory=historical_inventory,previous_inventory_sha256=historical_inventory_sha,
        current_inventory=immutable,current_inventory_sha256=expected,all_owned_records_identical=unchanged_owned,
        historical_guard=prior_guard,historical_guard_sha256=prior_guard_sha,
        preserved_history=history_path,preserved_history_sha256=history_sha,
        correction31_independent_checks=[dict(path=p,sha256=s,status=t) for p,s,t in external_checks],
        correction31_final_validator=dict(path=final_path,sha256=final_sha,integrity_status='passed'),
        scope='Only global inventory identity changes here; all owned literal source records and original semantic reviews are unchanged.')
    exercises={x['key']:x for x in inventory['exercises']}
    material={x['key']:x for x in inventory['material_source_units']}
    for row in ledger['exercises']:
        actual=exercises[row['inventory_key']]
        assert row['source']==actual['source'] and row['locator']==actual['locator']
        assert row['source_sha256']==actual['source_sha256']==digest(row['source'])
        assert row['source_text_sha256']==actual['text_sha256']
    for row in ledger['material_claims']:
        for key in row['source_unit_keys']:
            actual=material[key]
            assert actual['source_sha256']==digest(actual['source'])
            assert actual['source'] in ledger['scope_pages']
            # Component statements may differ from the whole paragraph; whole
            # claim-review entries preserve the literal paragraph identity.
            if row['id']==key+'::claim-review':
                assert row['statement_in_prose']==actual['source_text']

    reviews={}
    def collect(value):
        if isinstance(value,dict):
            path=value.get('file')
            if isinstance(path,str) and 'review' in path and path.endswith('.json') and 'sha256' in value:
                assert digest(path)==value['sha256'];reviews[path]=value['sha256']
            for child in value.values():collect(child)
        elif isinstance(value,list):
            for child in value:collect(child)
    collect(ledger)
    prior={};compiler={};raw_bindings=0
    def check_pairs(value,context=""):

        if isinstance(value,dict):
            if isinstance(value.get('path'),str) and isinstance(value.get('sha256'),str):
                assert digest(value['path'])==value['sha256']
                if any(word in context for word in ('prior','historical','original_review','component_review')):prior[value['path']]=value['sha256']
            for key,expected_sha in value.items():
                if not key.endswith('_sha256') or not isinstance(expected_sha,str):continue
                path=value.get(key[:-7])
                if not isinstance(path,str) or not (root/path).is_file():continue
                assert digest(path)==expected_sha,(path,key)
                if any(word in key for word in ('prior','historical','original_review','component_review')):
                    prior[path]=expected_sha
            for key,child in value.items():check_pairs(child,context+"/"+key)
        elif isinstance(value,list):
            for child in value:check_pairs(child,context)

    def verify_execution(manifest, manifest_sha, summaries=()):
        nonlocal raw_bindings
        assert digest(manifest)==manifest_sha
        raw=json.loads((root/manifest).read_text())
        rows=raw.get('files',[raw])
        assert rows and all(r.get('exit_code')==0 for r in rows),manifest
        for row in rows:
            source=row.get('file',row.get('source'))
            source_sha=row.get('sha256',row.get('source_sha256_after',row.get('sha256_after')))
            assert source and source_sha and digest(source)==source_sha,(manifest,source)
            assert row.get('source_unchanged',True) is True
            if 'source_sha256_before' in row:assert row['source_sha256_before']==source_sha
            if 'sha256_before' in row:assert row['sha256_before']==source_sha
            assert digest(row['log'])==row['log_sha256']
        for summary in summaries:
            source=summary.get('source',summary.get('file'))
            if source and source.endswith('.json'):source=summary.get('source')
            candidates=[r for r in rows if r.get('file',r.get('source'))==source] if source else rows
            assert candidates,(manifest,source)
            # Copies of raw compiler rows are checked against the actual
            # manifest, including command/workdir/time when present.
            fields=('file','sha256','exit_code','log','log_sha256','source_unchanged','actual_command','actual_workdir','started_at_utc','finished_at_utc','completed_at_utc','elapsed_seconds','source','source_sha256_before','source_sha256_after','sha256_before','sha256_after','command')
            copied=dict(summary)
            if copied.get('file','').endswith('.json'):
                copied.pop('file',None);copied.pop('sha256',None)
            assert any(all(copied[k]==row[k] for k in fields if k in copied and k in row) for row in candidates),manifest
            if 'actual_exit_code' in summary:assert summary['actual_exit_code']==0
            if 'source_sha256' in summary:assert digest(source)==summary['source_sha256']
            if 'raw_log' in summary:assert summary['raw_log']==candidates[0]['log']
            if 'raw_log_sha256' in summary:assert summary['raw_log_sha256']==candidates[0]['log_sha256']
            raw_bindings+=1
        compiler[manifest]=manifest_sha

    review_rows=[]
    for path,expected_sha in sorted(reviews.items()):
        reviewed=json.loads((root/path).read_text());check_pairs(reviewed)
        for section in ('source_sha256','proof_source_sha256','definition_dependency_source_sha256'):
            values=reviewed.get(section,{})
            if isinstance(values,dict):
                for source,source_sha in values.items():assert digest(source)==source_sha,(path,source)
        dependency_sources=reviewed.get('protected_dependency_evidence',{}).get('source_sha256',{})
        if isinstance(dependency_sources,dict):
            for source,source_sha in dependency_sources.items():assert digest(source)==source_sha,(path,source)
        evidence=reviewed.get('actual_standalone_evidence')
        if isinstance(evidence,str):
            verify_execution(evidence,reviewed['actual_standalone_evidence_sha256'])
        elif isinstance(evidence,list):
            for record in evidence:
                manifest=record.get('compiler_manifest')
                if manifest:
                    summaries=record.get('files',[record.get('record',record.get('raw_execution_record',record))])
                    verify_execution(manifest,record['compiler_manifest_sha256'],summaries)
                elif record.get('file','').endswith('.json'):
                    verify_execution(record['file'],record['sha256'],[record])
        review_rows.append(dict(review=path,review_sha256=expected_sha,historical_review_inventory_sha256=reviewed.get('inventory_sha256'),reviewer=reviewed.get('reviewer'),original_review_time_unchanged=reviewed.get('reviewed_at_utc'),scope='Current page/proof identities, exact mapped units, explicit prior paths and raw executions checked; historical inventory label is preserved and does not authorize changed clauses.'))

    raw_records={}
    for path in sorted((root/'book/coverage/checks').glob('modules*standalone.json')):
        actual=json.loads(path.read_text())
        for row in actual['files']:
            if row['exit_code']==0:
                raw_records.setdefault(row['file'],[]).append((str(path.relative_to(root)),row))
    proof_rows={}
    for source,row in ledger['proof_files'].items():
        evidence=row['standalone_compile_evidence']
        assert evidence['exit_code']==0 and evidence['source_unchanged'] and digest(source)==row['sha256']==evidence['sha256']
        assert digest(evidence['log'])==evidence['log_sha256']
        matches=[(manifest,raw) for manifest,raw in raw_records.get(source,[]) if evidence==raw]
        assert matches,source
        manifest,_=matches[-1]
        proof_rows[source]=dict(source_sha256=row['sha256'],compiler_manifest=manifest,compiler_manifest_sha256=digest(manifest),raw_log=evidence['log'],raw_log_sha256=evidence['log_sha256'])
    return dict(status='exact_current31_inventory_review_prior_reference_and_raw_execution_bindings_passed',inventory_identity_rebase=inventory_rebase,current_inventory=immutable,current_inventory_sha256=expected,exercise_count=len(ledger['exercises']),material_claim_count=len(ledger['material_claims']),referenced_reviews=review_rows,prior_review_and_history_references=prior,raw_compiler_manifests=compiler,raw_review_execution_binding_count=raw_bindings,proof_files=proof_rows,limits=['This is an identity and provenance check. Existing independent semantic decisions and original review timestamps are unchanged.','The inventory identity applies to current module mappings; old full inventory labels are historical provenance. No changed clause is reused solely because its page or inventory was rebased.','Standalone compiler success does not replace the fresh aggregate kernel and transitive axiom audit.'])
