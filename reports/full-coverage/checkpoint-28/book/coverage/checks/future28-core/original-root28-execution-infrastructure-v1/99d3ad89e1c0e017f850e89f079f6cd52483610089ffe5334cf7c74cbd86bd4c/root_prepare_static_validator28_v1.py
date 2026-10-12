"""Keep the original failed validator and add exact sequential hash reversal."""
from pathlib import Path
import hashlib, json
ROOT = Path('/home/oxrexkevin/SafetyBased')
original = ROOT/'book/validate.py'
destination = ROOT/'book/validate28_v1.py'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(original) == '29617e224d7105c9f504bb1b0373b2c33b92dd9c03a951c88c965ec27c25be86'
assert not destination.exists()
text = original.read_text()
marker = 'def clean_text(text):\n'
addition = '''def reverse_documented_corrections(source, corrections):
    """Reverse each full-page hash transition before removing book insertions."""
    restored = source
    for correction in reversed(corrections):
        if digest(restored) != correction['after_sha256']:
            raise ValueError('Correction after-page hash mismatch: ' + str(correction['correction_id']))
        for replacement in reversed(correction.get('replacements', [correction])):
            if restored.count(replacement['after']) != 1:
                raise ValueError('Correction replacement is not unique: ' + str(correction['correction_id']))
            restored = restored.replace(replacement['after'], replacement['before'], 1)
        if digest(restored) != correction['before_sha256']:
            raise ValueError('Correction before-page hash mismatch: ' + str(correction['correction_id']))
    return restored


'''
assert text.count(marker) == 1
text = text.replace(marker, addition+marker)
old = '''        restored=stripped
        for c in reversed(documented):
            for replacement in reversed(c.get('replacements', [c])):
                if restored.count(replacement['after'])!=1 or original.count(replacement['before'])!=1:
                    error('correction_source_mismatch',name,'Documented mathematical correction is not an exact unique source replacement',line=c['line'])
                else:
                    restored=restored.replace(replacement['after'],replacement['before'],1)
'''
new = '''        restored=stripped
        try:
            restored=remove_insertions(reverse_documented_corrections(doc.source,documented))
        except (KeyError,ValueError) as exc:
            error('correction_source_mismatch',name,'Documented mathematical corrections do not reverse through exact full-page hashes',detail=str(exc))
'''
assert text.count(old) == 1
text = text.replace(old,new)
text = text.replace("validator='book/validate.py',", "validator='book/validate28_v1.py',")
assert "validator='book/validate.py'," not in text
compile(text,str(destination),'exec')
with destination.open('x') as f: f.write(text)
assert sha(original) == '29617e224d7105c9f504bb1b0373b2c33b92dd9c03a951c88c965ec27c25be86'
print(json.dumps({'new_validator':str(destination.relative_to(ROOT)), 'sha256':sha(destination), 'original_failed_validator_unchanged':True}))
