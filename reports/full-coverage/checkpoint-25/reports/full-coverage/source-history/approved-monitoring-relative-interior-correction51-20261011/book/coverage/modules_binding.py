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

    immutable='book/coverage/inventory-after-correction28.json'
    expected='996b45a87bc0087c5a98b262762c22e1c45801d657521488250c8b77f12bd8f6'
    assert digest(immutable)==digest('book/coverage/inventory.json')==expected
    assert inventory==json.loads((root/immutable).read_text())
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
            source_sha=row.get('sha256',row.get('source_sha256_after'))
            assert source and source_sha and digest(source)==source_sha,(manifest,source)
            assert row.get('source_unchanged',True) is True
            if 'source_sha256_before' in row:assert row['source_sha256_before']==source_sha
            assert digest(row['log'])==row['log_sha256']
        for summary in summaries:
            source=summary.get('source',summary.get('file'))
            if source and source.endswith('.json'):source=summary.get('source')
            candidates=[r for r in rows if r.get('file',r.get('source'))==source] if source else rows
            assert candidates,(manifest,source)
            # Copies of raw compiler rows are checked against the actual
            # manifest, including command/workdir/time when present.
            fields=('file','sha256','exit_code','log','log_sha256','source_unchanged','actual_command','actual_workdir','started_at_utc','finished_at_utc')
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
    return dict(status='exact_current28_inventory_review_prior_reference_and_raw_execution_bindings_passed',current_inventory=immutable,current_inventory_sha256=expected,exercise_count=len(ledger['exercises']),material_claim_count=len(ledger['material_claims']),referenced_reviews=review_rows,prior_review_and_history_references=prior,raw_compiler_manifests=compiler,raw_review_execution_binding_count=raw_bindings,proof_files=proof_rows,limits=['This is an identity and provenance check. Existing independent semantic decisions and original review timestamps are unchanged.','The inventory identity applies to current module mappings; old full inventory labels are historical provenance. No changed clause is reused solely because its page or inventory was rebased.','Standalone compiler success does not replace the fresh aggregate kernel and transitive axiom audit.'])
