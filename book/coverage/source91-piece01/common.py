"""Exact, immutable records for the first bounded Source91 formal proof piece."""
from pathlib import Path
import hashlib
import json
import os
import tempfile

ROOT=Path(__file__).resolve().parents[3]


def path(name):
    p=Path(name)
    assert name and not p.is_absolute() and p.as_posix()==name
    assert not {'.git','.lake','..','__pycache__'}.intersection(p.parts)
    result=ROOT/p
    assert result.resolve().is_relative_to(ROOT) and not result.is_symlink()
    assert all(not q.is_symlink() for q in result.parents if q.is_relative_to(ROOT))
    return result


def sha(data):return hashlib.sha256(data).hexdigest()
def ref(name):return {'file':name,'sha256':sha(path(name).read_bytes())}
def read(name):return json.loads(path(name).read_bytes())
def exact(binding):
    assert ref(binding['file'])['sha256']==binding['sha256'],binding['file']
    return path(binding['file'])


def put(name,data):
    p=path(name)
    if p.exists():
        assert p.read_bytes()==data,'Immutable artifact differs: '+name
        return
    p.parent.mkdir(parents=True,exist_ok=True)
    fd,temporary=tempfile.mkstemp(prefix='.'+p.name+'-',dir=p.parent)
    try:
        with os.fdopen(fd,'wb') as output:
            output.write(data);output.flush();os.fsync(output.fileno())
        os.link(temporary,p)
        directory=os.open(p.parent,os.O_RDONLY|os.O_DIRECTORY)
        try:os.fsync(directory)
        finally:os.close(directory)
    finally:os.unlink(temporary)


def json_put(name,value):put(name,(json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode())
