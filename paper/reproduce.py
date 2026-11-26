"""Reproduce the named PDF twice from new directories and pack its TeX source."""
from pathlib import Path
from zipfile import ZipFile,ZipInfo,ZIP_DEFLATED
import tempfile,re,subprocess,hashlib,shutil,os
here=Path(__file__).resolve().parent
source=(here/'main.tex').read_bytes()
env=dict(os.environ, SOURCE_DATE_EPOCH='1795651200', FORCE_SOURCE_DATE='1', TZ='UTC')
with tempfile.TemporaryDirectory() as folder:
    copies=[]
    for name in ('a','b'):
        root=Path(folder)/name;root.mkdir()
        (root/'main.tex').write_bytes(source)
        for _ in range(2):
            subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','main.tex'],cwd=root,env=env,check=True,stdout=subprocess.DEVNULL)
        lines=(root/'main.log').read_text().splitlines()
        bad=[l for l in lines if 'Warning:' in l or 'Overfull ' in l or 'Missing character' in l]
        if bad:raise RuntimeError(bad)
        copies.append((root/'main.pdf').read_bytes())
    if copies[0]!=copies[1]:raise RuntimeError('Clean PDF copies differ.')
    (here/'main.pdf').write_bytes(copies[0])
    print('Named PDF',hashlib.sha256(copies[0]).hexdigest())
info=ZipInfo('main.tex',(2026,11,26,0,0,0));info.create_system=3;info.external_attr=0o100644<<16
with ZipFile(here/'arxiv-source.zip','w') as z:z.writestr(info,source,ZIP_DEFLATED,compresslevel=9)
with ZipFile(here/'arxiv-source.zip') as z: assert z.read('main.tex')==source and z.testzip() is None
print('TeX ZIP',hashlib.sha256((here/'arxiv-source.zip').read_bytes()).hexdigest())
