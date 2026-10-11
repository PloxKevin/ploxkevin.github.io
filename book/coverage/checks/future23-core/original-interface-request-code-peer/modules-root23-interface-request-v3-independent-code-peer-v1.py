from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,tempfile
R=Path('/home/oxrexkevin/SafetyBased')
N='book/coverage/checks/prepare_root_owner23_interfaces_request_v3.py'
O=Path('/tmp/root23-interface-request-v3-independent-modules-code-review-v1.json')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(R/N).read_text();tree=ast.parse(s)
assert h(R/N)=='523ea6ce684f1f4cfc7fd0e22d52204e54acd850dc936222d5bd018d2a9cc7f4'
assert not O.exists()
insert="""assert len(result['exact_replacements']) == 5
for replaced in result['exact_replacements']:
    original_name = replaced['original22_byte_copy']
    assert original_name.startswith('reports/full-coverage/owner22-originals-before-owner23-integration-v1/')
    assert sha(original_name) == replaced['before_sha256']
    report_hashes[original_name] = replaced['before_sha256']
"""
v2=(R/'book/coverage/checks/prepare_root_owner23_interfaces_request_v2.py').read_text()
assert s.replace(insert,'',1)==v2
assert "if p.is_file() and p.suffix in {'.json', '.log', '.html', '.txt'}:" in s
assert "excluded_full_external_reference_sha256" in s
assert "assert not (set(book_hashes.values()) & set(old_plan['excluded_full_external_reference_sha256']))" in s
assert "assert execution['actual_exit_code'] == 0" in s and "assert result['applied'] is True" in s
assert "assert not alias_dir.exists(); alias_dir.mkdir()" in s
assert "with target.open('xb')" in s and "with (ROOT / DEST).open('x')" in s
prefix_node=next(n for n in tree.body if isinstance(n,ast.For) and ast.unparse(n.target)=='prefix')
prefixes=ast.literal_eval(prefix_node.iter)
wrapper='reports/full-coverage/prepare-owner23-interface-request-execution-v1.json'
assert not any(Path(wrapper).name.startswith(prefix) for prefix in prefixes)
assert not any(Path(wrapper).with_suffix('.log').name.startswith(prefix) for prefix in prefixes)
assert "prepare-owner23-interface-request-execution" not in s
functions=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','ref','read'}]
archive_assert=next(n for n in tree.body if isinstance(n,ast.Assert) and "exact_replacements" in ast.unparse(n))
archive_loop=next(n for n in tree.body if isinstance(n,ast.For) and ast.unparse(n.target)=='replaced')
start=next(i for i,n in enumerate(tree.body) if isinstance(n,ast.Assign) and ast.unparse(n.targets[0])=='alias_dir')
end=next(i for i,n in enumerate(tree.body) if isinstance(n,ast.Assign) and ast.unparse(n.targets[0])=='folders')
alias_nodes=tree.body[start:end]
fixture_count=0
with tempfile.TemporaryDirectory(prefix='root23-interface-alias-peer-') as temporary:
    root=Path(temporary);base='book/coverage/checks/future23-core';(root/base).mkdir(parents=True)
    original=root/'reports/full-coverage/owner22-originals-before-owner23-integration-v1';original.mkdir(parents=True)
    replacements=[]
    for i,name in enumerate(('core.json','foundations.json','applied.json','modules.json','applied-promotions.json')):
        p=original/name;p.write_bytes((' {"original body":'+str(i)+',"reviewed_at":"old-time"}\n').encode())
        replacements.append({'original22_byte_copy':str(p.relative_to(root)),'before_sha256':h(p)})
    scope={'ROOT':root,'BASE':base,'Path':Path,'hashlib':hashlib,'json':json,'result':{'exact_replacements':replacements},'report_hashes':{},'book_hashes':{}}
    exec(compile(ast.Module(body=functions+[archive_assert,archive_loop],type_ignores=[]),'<actual-archive-guard-fixture>','exec'),scope)
    assert len(scope['report_hashes'])==5;fixture_count+=1
    # A duplicate original byte sequence gets one canonical content file plus both aliases.
    other=root/'reports/full-coverage/owner23-repeat.json';other.write_bytes((original/'core.json').read_bytes())
    scope['report_hashes'][str(other.relative_to(root))]=h(other)
    exec(compile(ast.Module(body=alias_nodes,type_ignores=[]),'<actual-original-byte-copy-fixture>','exec'),scope)
    aliases=scope['aliases'];assert len(aliases)==6 and len(list(scope['alias_dir'].iterdir()))==5;fixture_count+=1
    for a in aliases:
        x=root/a['original']['file'];y=root/a['canonical_original_byte_copy']['file']
        assert x.read_bytes()==y.read_bytes() and h(x)==h(y)==a['original']['sha256'];fixture_count+=1
    assert len(scope['book_hashes'])==6
    # Same guards reject count, outside archive path and mismatched historical bytes.
    for variant in ('count','path','digest'):
        records=[dict(r) for r in replacements]
        if variant=='count':records.pop()
        elif variant=='path':records[0]['original22_byte_copy']='reports/full-coverage/other/core.json'
        else:records[0]['before_sha256']='0'*64
        fake=dict(scope,result={'exact_replacements':records},report_hashes={})
        try:exec(compile(ast.Module(body=[archive_assert,archive_loop],type_ignores=[]),'<reject-original-byte-fixture>','exec'),fake)
        except AssertionError:fixture_count+=1
        else:raise AssertionError(variant)
# Review existing cut folders for extension compatibility without running preparation.
allowed={'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt'}
folders=('future23-core','future23-monitoring','future23-scenario-source50','future23-monitoring-source51','foundations-future23','applied-future23','modules-future23','root-source-batch49','root-source-batch50','root-source-batch51')
for folder in folders:
    for p in (R/'book/coverage/checks'/folder).rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts:assert p.suffix in allowed,str(p)
out={'status':'independent_root23_postintegration_interface_request_v3_code_review_passed_requires_actual_output_peer','checked_at_utc':datetime.now(timezone.utc).isoformat(),'helper':{'file':N,'sha256':h(R/N)},'preserved_unexecuted_v2':{'file':'book/coverage/checks/prepare_root_owner23_interfaces_request_v2.py','sha256':h(R/'book/coverage/checks/prepare_root_owner23_interfaces_request_v2.py'),'decision':'Needs explicit copy/hash inclusion of five original22 archive bytes; result JSON pointers alone do not establish that request closure.'},'preserved_unexecuted_v1':{'file':'book/coverage/checks/prepare_root_owner23_interfaces_request_v1.py','sha256':h(R/'book/coverage/checks/prepare_root_owner23_interfaces_request_v1.py'),'decision':'Browser PNGs are outside freezer additional-input suffix allowlist; they belong to separate postfreeze publication evidence.'},'required_actual_wrapper_name':wrapper,'required_actual_wrapper_raw_log':str(Path(wrapper).with_suffix('.log')),'pure_filesystem_fixture_count':fixture_count,'mechanical_findings':['The exact v2-to-v3 delta copies only five original22 archive bytes after exact before_sha256 checks.','Actual --apply exit0 and applied result are prerequisites; copied original JSON/log bodies and commands/times/statuses remain unchanged.','Content-hash aliases preserve byte equality and every original path, including duplicate byte sequences and preparation failures.','Only new request/aliases are written; no source, selected proof or owner ledger modification is performed.','The required actual wrapper prefix is outside every scanned report prefix, so its open raw log cannot enter additional_frozen_inputs.','Full external reference hashes are rejected, browser PNGs stay outside textual frozen extras, and current cut-folder suffixes match the freezer allowlist.'],'errors':[],'scope':'Independent code and isolated synthetic-filesystem fixtures only. No actual postintegration preparation, owner copy, Lean compilation or checkpoint23 audit was executed by this checker. Exact actual request/output/plan peers remain separate.'}
O.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'report':str(O),'sha256':h(O),'fixture_count':fixture_count}))
