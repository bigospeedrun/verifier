"""Offline package controls; optional Lean check restricted to own GitHub Actions."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CH = ROOT / 'challenges/other-snaky'

def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'MANIFEST.json').read_text())['sha256']
    inventory = {p.name for p in HERE.iterdir() if p.is_file() and p.name != 'MANIFEST.json'}
    require(inventory == set(manifest), 'package inventory')
    require(not any(p.is_symlink() or p.is_dir() for p in HERE.iterdir()), 'plain flat package')
    for name, sha in manifest.items():
        require(digest(HERE / name) == sha, 'package hash: ' + name)
    pins = json.loads((HERE / 'source-hashes.json').read_text())
    for name, sha in pins['challenge'].items():
        require(digest(CH / name) == sha, 'challenge hash: ' + name)
    profile = (ROOT / 'profiles/lake-manifest.json').read_bytes().replace(b'\r\n', b'\n')
    require(hashlib.sha256(profile).hexdigest() == pins['profile_sha256_lf'], 'dependency manifest')
    source = (HERE / 'SnakyTwentyOne.lean.txt').read_text(encoding='utf-8')
    require(hashlib.sha256(source.encode()).hexdigest() == pins['upstream_sha256'], 'upstream archive')
    prefix = source.split('\nnamespace SnakyPrototype\nopen OrdinaryStrategy')[0]
    model = (CH / 'Model.lean').read_text(encoding='utf-8')
    imports = ['Mathlib.Data.Finset.Card', 'Mathlib.Data.Int.Basic',
               'Mathlib.Data.Fintype.Prod', 'Mathlib.Algebra.Group.Prod']
    expected = prefix.replace('import Mathlib\n', ''.join('import '+m+'\n' for m in imports), 1)
    require(model.split('-/\n', 1)[1] == expected + '\nend OAI\n', 'unchanged definition block with narrow imports')
    statement = (CH / 'Statement.lean').read_text(encoding='utf-8')
    original_target = source.split('theorem snaky_winning_strategy_21_with_legal_states :\n',1)[1].split(' := by')[0]
    target = statement.split('def Bound (n : ℕ) : Prop :=\n',1)[1].split('\n\nend')[0]
    # Compare the entire proposition, not selected substrings.
    require(' '.join(target.split()) == ' '.join(original_target.replace('21','n').replace('20','(n - 1)').split()), 'full parameter substitution')
    for text in (model, statement, (HERE / 'Controls.lean').read_text(encoding='utf-8')):
        code = re.sub(r'/\-.*?\-/', '', text, flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        require(not re.search(r'\b(sorry|axiom|unsafe)\b', code), 'proof placeholder or extra axiom')
    # Independent finite geometry and timeline controls. These prove no strategy.
    shape = {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}
    transforms = [lambda x,y:(x,y), lambda x,y:(y,x), lambda x,y:(x,-y),
                  lambda x,y:(-y,x), lambda x,y:(-x,y), lambda x,y:(y,-x),
                  lambda x,y:(-x,-y), lambda x,y:(-y,-x)]
    orientations = set()
    for f in transforms:
        image = {f(x,y) for x,y in shape}
        mx, my = min(x for x,y in image), min(y for x,y in image)
        orientations.add(frozenset((x-mx,y-my) for x,y in image))
        require(len(image) == 6, 'orientation loses a cell')
    require(len(orientations) == 8, 'all eight distinct orientations')
    # Maker ignores the reply at this index until its NEXT move.
    def play(maker, replies, n):
        m,b = set(),set()
        states = [(set(m),set(b))]
        legal = True
        for k in range(n):
            x = maker[k]
            legal &= x not in m and x not in b
            m.add(x)
            if k+1 < n:
                legal &= replies[k] not in m and replies[k] not in b
            b.add(replies[k])
            states.append((set(m),set(b)))
        return states, legal
    maker = sorted(shape)
    outside = [(100,k) for k in range(6)]
    cases = 0
    for final in list(shape) + [(100,5),(-100,-100)]:
        states, legal = play(maker, outside[:5]+[final],6)
        require(legal and states[-1][0] == shape and states[-1][0].isdisjoint(states[-2][1]), 'unrestricted final reply')
        cases += 1
    _, legal = play(maker,[maker[0]]+outside[1:],6)
    require(not legal,'earlier collision must be illegal')
    _, legal = play([maker[0]]*6,outside,6)
    require(not legal,'duplicate Maker claims must be illegal')
    require(all(len(set(maker[:n])) < 6 for n in range(6)), 'fewer than six claims cannot own shape')
    print('PASS: package hashes, source extraction, full target substitution and dependency pin')
    print(f'PASS: 8 orientations, {cases} final-reply controls, earlier collisions, duplicate claims and six-cell lower-bound sanity')
    print('Finite controls are not a strategy proof or a Comparator receipt.')
    if args.lean:
        require(os.environ.get('GITHUB_ACTIONS') == 'true', 'Lean runs only on own GitHub Actions')
        with tempfile.TemporaryDirectory(prefix='snaky-statement-') as temp:
            project = Path(temp)
            shutil.copytree(CH,project/'challenges/other-snaky')
            shutil.copyfile(HERE/'Controls.lean',project/'Controls.lean')
            (project/'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
            (project/'lakefile.toml').write_text('name = "snaky_statement"\nversion = "0.1.0"\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "d13f23b723b8a846827a245b89c10fc7d3f11612"\n')
            (project/'lake-manifest.json').write_bytes(profile)
            subprocess.run(['lake','exe','cache','get',*imports],cwd=project,check=True)
            # Compile only the two trusted source modules before the controls.
            for path in ['challenges/other-snaky/Model','challenges/other-snaky/Statement']:
                output = project/'.lake/build/lib/lean'/Path(path+'.olean')
                output.parent.mkdir(parents=True,exist_ok=True)
                subprocess.run(['lake','env','lean','-o',str(output),path+'.lean'],cwd=project,check=True)
            result = subprocess.run(['lake','env','lean','Controls.lean'],cwd=project,text=True,capture_output=True)
            print(result.stdout)
            print(result.stderr)
            require(result.returncode == 0 and 'sorryAx' not in result.stdout and 'declaration uses' not in result.stdout,'Lean controls and axioms')
            for name in ('not_bound_zero', 'baseline_adapter'):
                match = re.search(r"'BigOSpeedrun.Snaky\."+name+r"' depends on axioms: \[([^\]]*)\]", result.stdout)
                if match:
                    axioms = {a.strip() for a in match.group(1).split(',') if a.strip()}
                    require(axioms <= {'propext','Classical.choice','Quot.sound'},'unexpected axiom')
                else:
                    require("'BigOSpeedrun.Snaky."+name+"' does not depend on any axioms" in result.stdout,'missing axiom report')
            print('PASS: Lean zero-bound refutation, six-cell count and conditional baseline adapter')

if __name__ == '__main__':
    main()
