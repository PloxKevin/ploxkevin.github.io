#!/usr/bin/env python3
"""Read primary references into TMP only; never install or classify ledger rows."""
import concurrent.futures, datetime, hashlib, json, pathlib, subprocess, time, urllib.request
ROOT=pathlib.Path('/home/oxrexkevin/SafetyBased')
OUT=pathlib.Path('/tmp/foundations-basics-eight-primary-bibliography28-v1')
URLS={
 'hammack':'https://richardhammack.github.io/BookOfProof/',
 'velleman':'https://www.cambridge.org/highereducation/books/how-to-prove-it/6D2965D625C6836CD4A785A2C843B3DA',
 'velleman-front':'https://assets.cambridge.org/97811084/39534/frontmatter/9781108439534_frontmatter.pdf',
 'mit':'https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-spring-2015/resources/mit6_042js15_textbook/',
 'mit-pdf':'https://ocw.mit.edu/courses/6-042j-mathematics-for-computer-science-spring-2015/mit6_042js15_textbook.pdf',
 'abbott':'https://link.springer.com/book/10.1007/978-1-4939-2712-8',
 'abbott-front':'https://link.springer.com/content/pdf/bfm:978-1-4939-2712-8/1',
 'lebl':'https://www.jirka.org/ra/',
 'lebl-pdf':'https://www.jirka.org/ra/realanal.pdf',
 'boyd':'https://web.stanford.edu/~boyd/cvxbook/',
 'boyd-pdf':'https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf',
 'boyd-coauthor-pdf':'https://www.seas.ucla.edu/~vandenbe/cvxbook/bv_cvxbook.pdf',
 'arora':'https://theory.cs.princeton.edu/complexity/',
 'arora-chapter':'https://www.cambridge.org/core/books/abs/computational-complexity/np-and-np-completeness/D1D3CDF090A9D3451ACD092A307050C8',
 'sutton-original':'http://incompleteideas.net/book/the-book-2nd.html',
 'sutton-https':'https://incompleteideas.net/book/the-book-2nd.html',
 'sutton-publisher':'https://mitpress.mit.edu/9780262039246/reinforcement-learning/',
 'sutton-toc':'https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/10094/Toc.pdf?dl=1',
 'sutton-draft':'https://www.incompleteideas.net/book/bookdraft2018mar21.pdf',
}
def sha(b):return hashlib.sha256(b).hexdigest()
def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def protected():
 inv=json.loads((ROOT/'book/coverage/inventory.json').read_text())
 selected=json.loads((ROOT/'reports/full-coverage/checkpoint-28-selection.json').read_text())
 names=list(selected['proof_files'])+list(inv['source_sha256'])
 names+=['book/coverage/inventory.json','book/coverage/material-corrections.json','reports/full-coverage/checkpoint-28-selection.json']
 names+=['book/coverage/'+x+'.json' for x in ['core','foundations','applied','modules','applied-promotions']]
 assert len(selected['proof_files'])==1186
 return {n:sha((ROOT/n).read_bytes()) for n in sorted(set(names))}
def fetch(item):
 name,url=item; started=stamp();t=time.monotonic();row={'id':name,'requested_url':url,'started_at_utc':started}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (bibliographic-source-verification)'})
  with urllib.request.urlopen(req,timeout=25) as r:
   b=r.read(25000001);assert len(b)<=25000000
   row.update(http_status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'),bytes=len(b),sha256=sha(b))
  ext='.pdf' if b.startswith(b'%PDF') else '.html'
  p=OUT/(name+ext);p.write_bytes(b);row['offline_file']=str(p)
  if ext=='.pdf':
   q=OUT/(name+'.txt');command=['pdftotext','-layout',str(p),str(q)]
   cp=subprocess.run(command,capture_output=True);row['text_conversion']={'command':command,'exit_code':cp.returncode,'raw_output_sha256':sha(cp.stdout+cp.stderr)}
   if cp.returncode==0:row['offline_text']={'file':str(q),'sha256':sha(q.read_bytes())}
 except Exception as e:row['error']=repr(e)
 row.update(ended_at_utc=stamp(),elapsed_seconds=time.monotonic()-t)
 return row
def main():
 assert not OUT.exists(),str(OUT);before=protected();OUT.mkdir()
 with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:rows=list(pool.map(fetch,URLS.items()))
 after=protected();errors=[n for n in before if before[n]!=after[n]]
 data={'schema_version':1,'scope':'Primary-reference retrieval only; no proof approval, no ledger/source/compiler/website write. Full remote originals remain TMP offline.','results':rows,'protected_before':before,'protected_after':after,'protection_errors':errors}
 (OUT/'primary-http-receipts-v1.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
 for r in rows:print(json.dumps({k:r[k] for k in ['id','http_status','bytes','sha256','error'] if k in r},ensure_ascii=False),flush=True)
 assert not errors,errors
if __name__=='__main__':main()
