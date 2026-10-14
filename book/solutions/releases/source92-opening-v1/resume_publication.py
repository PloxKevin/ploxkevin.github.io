"""Resume the pinned stage, explicitly including its reviewed ignored log files."""
from pathlib import Path
import runpy
import subprocess

ROOT=Path(__file__).resolve().parents[4]


def main():
    loaded=runpy.run_path(str(ROOT/'book/solutions/releases/source92-opening-v1/publish_recovery.py'))
    h=loaded['h'];plan=h.read(loaded['PLAN']);pub=loaded['PUB']
    assert loaded['git']('rev-parse','HEAD')==plan['expected_head']
    assert set(loaded['git']('diff','--cached','--name-only').splitlines())<={r['file'] for r in plan['files']}
    for row in plan['files']:
        assert h.ref(row['source']['file'])==row['source']
        assert h.sha((pub/row['file']).read_bytes())==row['after_sha256']
    logs=[r['file'] for r in plan['files'] if r['file'].endswith('.log')]
    for offset in range(0,len(logs),200):
        subprocess.run(['git','add','-f','--',*logs[offset:offset+200]],cwd=pub,check=True)
    loaded['stage'](h.ref(loaded['PLAN'])['sha256'])


if __name__=='__main__':main()
