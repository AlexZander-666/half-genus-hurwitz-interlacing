"""Build project sources from an empty temporary directory and replay every local module."""
from pathlib import Path
from tempfile import TemporaryDirectory
import os, shutil, subprocess, hashlib, sys
source=Path(__file__).resolve().parent
packages=Path(sys.argv[1]).resolve(strict=True)
os.environ['PATH']=str(Path.home()/'.elan'/'bin')+':'+os.environ['PATH']
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def run(args,cwd):
    result=subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(result.stdout,end='',flush=True)
    if any(line.startswith(('warning: HalfWords', 'warning: Hurwitz', 'warning: HalfGenus')) for line in result.stdout.splitlines()):
        raise ValueError('A local Lean source emitted a warning')
    result.check_returncode()
modules=['Hurwitz.Connectivity','Hurwitz.MatchingWords','Hurwitz.Charge','Hurwitz.WordWeights',
         'Hurwitz.Paths','HalfWords.Source','HalfWords.Canonical','HalfWords.Hive',
         'HalfWords.Surgery','HalfWords.Coordinates','HalfWords.Flip','HalfWords.Join','HalfWords.Cut','HalfWords.ActualSurgery','HalfWords.Skip','HalfWords.Fresh','HalfWords.UniqueChild','HalfWords.Pivot','HalfWords.ComponentCount','HalfWords.Distance','HalfWords.StepCount','HalfWords.Excess','HalfWords.Homogeneity','HalfWords.ZeroBudget','HalfWords.Locality','HalfWords.Shuffle','HalfWords.Profiles','HalfWords.CoreProfile','HalfWords.CutType','HalfWords.CutMultiplicity','HalfWords.PivotProfile','HalfWords.ActivePartners','HalfWords.ActiveRecurrence','HalfWords.InactiveBounds','HalfWords.ActiveMaximum','HalfWords.UnboundedRecurrence','HalfWords.PivotCoordinates','HalfWords.DistanceZero','HalfWords.JetRows','HalfWords.JetProfile','HalfWords.ChildBudget','HalfWords.ProfileInduction','HalfWords.OriginalCorollary','HalfWords.Series','HalfWords.ScalarSeries','HalfWords.Discriminant','HalfWords.ClassicalSeries','HalfWords.CoefficientRecurrence','HalfWords.PhysicalPolynomial','HalfGenus.Energy','HalfGenus.Gegenbauer','HalfGenus.Contact','HalfGenus.Mesh','HalfGenus.RealRoots','HalfGenus.Interlacing','HalfGenus.Verified','HalfWords.OrthogonalValues','HalfWords.Mobius','HalfWords.HurwitzVerified','HalfWords.ZeroRows','HalfWords.BinomialRows','HalfWords.BinomialFormula','HalfWordsAudit']
with TemporaryDirectory(prefix='half-words-cold-') as work:
    root=Path(work)
    for name in ['lakefile.toml','lake-manifest.json','lean-toolchain','HalfWordsAudit.lean']:
        shutil.copyfile(source/name,root/name)
    for name in ['HalfWords','Hurwitz','HalfGenus']:
        shutil.copytree(source/name,root/name)
    (root/'.lake').mkdir()
    (root/'.lake'/'packages').symlink_to(packages,target_is_directory=True)
    run(['lake','-KwarningAsError=true','build','HalfWordsAudit'],root)
    for module in modules:
        path=Path(*module.split('.'))
        lean=root/path.with_suffix('.lean')
        obj=root/'.lake'/'build'/'lib'/'lean'/path.with_suffix('.olean')
        run(['lake','env','leanchecker',module],root)
        print(f'PASS {module} source={digest(lean)} object={digest(obj)}',flush=True)
print(f'PASS {len(modules)} local modules; no preexisting local objects were copied.')
