import importlib.util,pathlib,json,concurrent.futures
P=pathlib.Path('/tmp/fetch-foundations-basics-eight-primary-bibliography28-v1.py')
s=importlib.util.spec_from_file_location('retrieval',P);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.OUT=pathlib.Path('/tmp/foundations-basics-primary-followups28-v1')
m.URLS={
 'arora-http':'http://theory.cs.princeton.edu/complexity/',
 'arora-author':'https://www.boazbarak.org/CS121/COMPLEXITY/book.pdf',
 'velleman-front-http':'http://assets.cambridge.org/97811084/39534/frontmatter/9781108439534_frontmatter.pdf',
 'velleman-front-hardback':'https://assets.cambridge.org/97811084/24189/frontmatter/9781108424189_frontmatter.pdf',
 'velleman-author':'https://djvelleman.people.amherst.edu/',
 'sutton-current-pdf-http':'http://incompleteideas.net/book/RLbook2020.pdf',
 'abbott-front-encoded':'https://link.springer.com/content/pdf/bfm%3A978-1-4939-2712-8/1?download=1',
}
m.main()
