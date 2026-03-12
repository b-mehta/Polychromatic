#!/usr/bin/env python3
"""
Batch-submit proofs from Combi.lean to Aristotle for golfing.

Overview
--------
Aristotle (https://aristotle.harmonic.fun) is an automated theorem prover.
This script extracts lemmas from Combi.lean and submits them to Aristotle
to find shorter proofs. Results are saved as result_<name>.lean files in
the same directory, and submission status is tracked in status.json.

How it works
------------
For each eligible proof (non-sorry, ≥ min-size lines):

1. **Extract**: Parse Combi.lean to find all lemma/def declarations, their
   signatures, proof bodies, and line ranges.

2. **Dependency resolution**: BFS over the file to find all lemmas that the
   target transitively references. These are included in the scratch file
   with their proofs replaced by `admit`, so Aristotle knows their types
   but doesn't need to re-prove them.

3. **Scratch file creation**: Build a minimal .lean file containing:
   - Import stubs (Mathlib imports + stub definitions for IsPolychrom,
     HasPolychromColouring, polychromNumber, etc.)
   - Section/variable declarations that are in scope
   - Transitive dependencies with proofs replaced by `admit`
   - The target lemma with its proof replaced by `sorry`
   This avoids sending the full 2500-line Combi.lean to Aristotle.

4. **Submission**: Send the scratch file to Aristotle via `aristotlelib`
   SDK. Aristotle attempts to prove the sorry'd lemma and writes the
   result to result_<name>.lean.

5. **Status tracking**: Results are recorded in status.json so already-
   completed proofs are skipped on re-runs. Proofs are submitted in
   batches of --batch size concurrently.

Requirements
------------
- `aristotlelib` Python package (install in a dedicated venv/pyenv)
- Aristotle API key configured for aristotlelib

Usage
-----
  PYENV_VERSION=aristotle python3 golf_batch.py              # submit all ≥5 lines
  PYENV_VERSION=aristotle python3 golf_batch.py --min-size 3  # submit all ≥3 lines
  PYENV_VERSION=aristotle python3 golf_batch.py --batch 5     # 5 concurrent submissions
  PYENV_VERSION=aristotle python3 golf_batch.py --start-from case2b_coverage_gen
  PYENV_VERSION=aristotle python3 golf_batch.py --only foo,bar,baz
  PYENV_VERSION=aristotle python3 golf_batch.py --list        # dry run: list eligible proofs

Output files
------------
  scratch_<name>.lean  - the minimal file sent to Aristotle (can be deleted)
  result_<name>.lean   - Aristotle's response with its proof attempt
  status.json          - tracks which proofs have been submitted and their results

Use compare.py to evaluate which Aristotle results are actually shorter.
"""

import asyncio
import argparse
import json
import os
import re
import sys
from pathlib import Path

import aristotlelib

COMBI_PATH = Path(__file__).parent.parent / "Combi.lean"
RESULTS_DIR = Path(__file__).parent
STATUS_FILE = RESULTS_DIR / "status.json"

# Stub definitions to replace `import Polychromatic.*` so Aristotle doesn't
# pull in the full project (which has files incompatible with its mathlib).
IMPORT_STUBS = """\
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.ZMod.Basic

open Finset Pointwise

set_option autoImplicit true

section Stubs

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k

def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ

@[simp] lemma hasPolychromColouring_univ [Fintype G] :
    HasPolychromColouring G (Finset.univ : Finset G) := by admit

lemma HasPolychromColouring.of_image {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F)
    {K : Type*} {S : Finset G}
    (h : HasPolychromColouring K (S.image φ)) :
    HasPolychromColouring K S := by admit

noncomputable def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}

lemma polychromNumber_vadd {n : G} {S : Finset G} :
    polychromNumber (n +ᵥ S) = polychromNumber S := by admit

lemma le_polychromNumber {S : Finset G} {n : ℕ} (hn : HasPolychromColouring (Fin n) S) :
    n ≤ polychromNumber S := by admit

lemma hasPolychromColouring_fin_of_le {S : Finset G} {n : ℕ}
    (hn : n ≠ 0) (hS : n ≤ polychromNumber S) :
    HasPolychromColouring (Fin n) S := by admit

lemma polychromNumber_iso {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [EquivLike F G H] [AddEquivClass F G H] (φ : F)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S := by admit

end Stubs

set_option autoImplicit false

"""


def extract_proofs(filepath: Path) -> list[dict]:
    """Extract all proofs with their line ranges from Combi.lean."""
    with open(filepath) as f:
        lines = f.readlines()

    decl_pat = re.compile(r'^(private\s+)?(theorem|lemma|def|instance)\s+(\S+)')
    proofs = []
    i = 0
    while i < len(lines):
        m = decl_pat.match(lines[i])
        if m:
            name = m.group(3)
            start = i  # 0-indexed

            # Find ':= by', ':= fun', ':= if', ':= sorry', or plain ':='
            j = i
            has_proof = False
            is_sorry = False
            is_term = False
            by_line = -1
            while j < len(lines):
                if ':= by' in lines[j]:
                    has_proof = True
                    by_line = j
                    break
                if ':= sorry' in lines[j]:
                    is_sorry = True
                    break
                if ':= fun' in lines[j] or ':= if' in lines[j]:
                    has_proof = True
                    by_line = j
                    break
                # Plain term-mode definition (e.g. `def foo := expr`)
                if ':=' in lines[j] and not any(
                    p in lines[j] for p in [':= by', ':= sorry', ':= fun', ':= if']
                ):
                    is_term = True
                    by_line = j
                    break
                # Match-expression definition (equation compiler, e.g. `| 0 => ...`)
                if j > i and re.match(r'^\s+\|', lines[j]):
                    is_term = True
                    by_line = i  # include from declaration start
                    break
                if j > i and decl_pat.match(lines[j]):
                    break
                j += 1

            if has_proof or is_term:
                # Find end of proof/definition
                k = by_line + 1
                while k < len(lines):
                    line = lines[k]
                    if decl_pat.match(line):
                        break
                    if re.match(r'^(section|end|namespace|/-!|/--|open|variable|#)', line):
                        break
                    k += 1
                proof_lines = k - start
                proofs.append({
                    'name': name,
                    'start': start,        # 0-indexed inclusive
                    'by_line': by_line,     # 0-indexed, line with ':= by'
                    'end': k,              # 0-indexed exclusive
                    'size': proof_lines,
                    'is_sorry': is_sorry,
                    'is_term': is_term,    # term-mode def, include verbatim
                })
                i = k
                continue
            elif is_sorry:
                proofs.append({
                    'name': name,
                    'start': start,
                    'by_line': j,
                    'end': j + 1,
                    'size': j + 1 - start,
                    'is_sorry': True,
                })
                i = j + 1
                continue
        i += 1
    return proofs


def find_dependencies(filepath: Path, proof: dict, all_proofs: list[dict]) -> list[dict]:
    """Find proofs that the target proof transitively references."""
    with open(filepath) as f:
        lines = f.readlines()

    def direct_deps(p: dict) -> list[dict]:
        body = ''.join(lines[p['start']:p['end']])
        deps = []
        for q in all_proofs:
            if q['name'] == p['name']:
                continue
            if q['start'] >= p['start']:
                continue  # only look at earlier declarations
            if re.search(r'\b' + re.escape(q['name']) + r'\b', body):
                deps.append(q)
        return deps

    # BFS for transitive dependencies
    seen = {proof['name']}
    queue = direct_deps(proof)
    result = []
    while queue:
        dep = queue.pop(0)
        if dep['name'] in seen:
            continue
        seen.add(dep['name'])
        result.append(dep)
        queue.extend(direct_deps(dep))

    # Sort by file order so definitions come before uses
    result.sort(key=lambda p: p['start'])
    return result


def create_scratch_file(filepath: Path, proof: dict, output_path: Path,
                        all_proofs: list[dict] | None = None):
    """Create a minimal file with just the target lemma (sorry'd) and its
    dependencies (admitted), plus stubs for imported definitions.

    This avoids sending 2500 lines to Aristotle, which causes env errors.
    """
    with open(filepath) as f:
        lines = f.readlines()

    out = [IMPORT_STUBS]

    # Find section variables that are in scope for this proof
    # (e.g. `variable (m : ℕ)`)
    for idx in range(proof['start']):
        line = lines[idx]
        if line.startswith('variable '):
            out.append(line)
        elif line.startswith('section ') or line.startswith('end '):
            out.append(line)

    out.append('\n')

    # Add dependencies as admitted lemmas (or verbatim for term-mode defs)
    if all_proofs:
        deps = find_dependencies(filepath, proof, all_proofs)
        for dep in deps:
            if dep.get('is_term'):
                # Term-mode definition: include verbatim
                for idx in range(dep['start'], dep['end']):
                    out.append(lines[idx])
            else:
                # Proof: include signature but replace proof with admit
                for idx in range(dep['start'], dep['end']):
                    if idx == dep['by_line']:
                        by_line_text = lines[idx]
                        for pattern in [':= by', ':= fun', ':= if']:
                            if pattern in by_line_text:
                                out.append(by_line_text[:by_line_text.index(pattern)]
                                           + ':= by admit\n')
                                break
                        break
                    else:
                        out.append(lines[idx])
            out.append('\n')

    # Add the target proof as sorry
    for idx in range(proof['start'], proof['end']):
        if idx == proof['by_line']:
            by_line_text = lines[idx]
            for pattern in [':= by', ':= fun', ':= if']:
                if pattern in by_line_text:
                    out.append(by_line_text[:by_line_text.index(pattern)]
                               + ':= sorry\n')
                    break
            break
        else:
            out.append(lines[idx])

    with open(output_path, 'w') as f:
        f.writelines(out)


def load_status() -> dict:
    if STATUS_FILE.exists():
        with open(STATUS_FILE) as f:
            return json.load(f)
    return {}


def save_status(status: dict):
    with open(STATUS_FILE, 'w') as f:
        json.dump(status, f, indent=2)


async def submit_proof(proof: dict, scratch_path: Path, output_path: Path,
                       completed: dict) -> tuple[str, str]:
    """Submit a single proof to Aristotle via SDK and return (name, status)."""
    name = proof['name']

    try:
        with open(scratch_path) as f:
            content = f.read()

        solution_path = await aristotlelib.Project.prove_from_file(
            input_content=content,
            auto_add_imports=False,
            validate_lean_project=False,
            output_file_path=str(output_path),
        )

        if not output_path.exists():
            result = "failed: no output"
            print(f"  ✗ {name}: no output file produced")
        else:
            result_text = output_path.read_text()
            if 'sorry' not in result_text:
                result = "proved"
                print(f"  ✓ {name} PROVED")
            elif 'The following was proved' in result_text[:500]:
                result = "proved"
                print(f"  ✓ {name} PROVED (with header)")
            else:
                result = "still_sorry"
                print(f"  ~ {name} returned but still sorry")
    except Exception as e:
        result = f"failed: {e}"
        print(f"  ✗ {name} failed: {e}")

    completed[name] = result
    return name, result


def _format_elapsed(seconds: float) -> str:
    m, s = divmod(int(seconds), 60)
    if m >= 60:
        h, m = divmod(m, 60)
        return f"{h}h{m:02d}m"
    return f"{m}m{s:02d}s"


async def _progress_printer(total: int, completed: dict, names: list[str],
                             start_time: float):
    """Print periodic progress updates while waiting for submissions."""
    import time
    while len(completed) < total:
        await asyncio.sleep(60)
        elapsed = time.time() - start_time
        done = len(completed)
        pending = [n for n in names if n not in completed]
        pending_str = ", ".join(pending[:4])
        if len(pending) > 4:
            pending_str += f", ... (+{len(pending) - 4})"
        print(f"  ⏳ {done}/{total} complete, {_format_elapsed(elapsed)} elapsed. "
              f"Waiting: {pending_str}")


async def run_batch(proofs: list[dict], all_proofs: list[dict], batch_size: int):
    """Submit a batch of proofs concurrently."""
    import time
    status = load_status()

    tasks = []
    for proof in proofs:
        name = proof['name']
        if name in status and status[name].get('result') in ('proved', 'complete'):
            print(f"  Skipping {name} (already done)")
            continue

        scratch_path = RESULTS_DIR / f"scratch_{name}.lean"
        output_path = RESULTS_DIR / f"result_{name}.lean"

        create_scratch_file(COMBI_PATH, proof, scratch_path, all_proofs)

        tasks.append((proof, scratch_path, output_path))

    # Process in batches
    for i in range(0, len(tasks), batch_size):
        batch = tasks[i:i + batch_size]
        names = [p['name'] for p, _, _ in batch]
        print(f"\nBatch {i // batch_size + 1}: {len(batch)} proofs")
        print(f"  Submitting: {', '.join(names)}")

        completed = {}
        start_time = time.time()

        # Launch proof submissions + progress printer concurrently
        proof_tasks = [
            submit_proof(p, sp, op, completed) for p, sp, op in batch
        ]
        progress_task = asyncio.create_task(
            _progress_printer(len(batch), completed, names, start_time)
        )

        results = await asyncio.gather(*proof_tasks)
        progress_task.cancel()

        elapsed = time.time() - start_time
        print(f"  Batch done in {_format_elapsed(elapsed)}")

        for (proof, _, _), (_, result) in zip(batch, results):
            status[proof['name']] = {
                'result': result,
                'size': proof['size'],
                'lines': f"L{proof['start']+1}-{proof['end']}",
            }
        save_status(status)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--batch', type=int, default=10, help='Batch size')
    parser.add_argument('--min-size', type=int, default=5, help='Min proof lines')
    parser.add_argument('--start-from', type=str, help='Start from this proof name')
    parser.add_argument('--only', type=str, help='Comma-separated list of proof names')
    parser.add_argument('--list', action='store_true', help='Just list eligible proofs')
    args = parser.parse_args()

    os.chdir(COMBI_PATH.parent.parent.parent)  # cd to Lean/

    all_proofs = extract_proofs(COMBI_PATH)

    # Filter: non-sorry, non-term-mode, ≥ min_size lines
    eligible = [p for p in all_proofs
                if not p.get('is_sorry') and not p.get('is_term') and p['size'] >= args.min_size]

    if args.only:
        names = set(args.only.split(','))
        eligible = [p for p in eligible if p['name'] in names]

    if args.start_from:
        idx = next((i for i, p in enumerate(eligible) if p['name'] == args.start_from), 0)
        eligible = eligible[idx:]

    if args.list:
        for p in eligible:
            print(f"{p['size']:4d} lines  L{p['start']+1:4d}-{p['end']:4d}  {p['name']}")
        print(f"\nTotal: {len(eligible)} eligible proofs")
        return

    print(f"Eligible proofs: {len(eligible)} (≥{args.min_size} lines, non-sorry)")
    asyncio.run(run_batch(eligible, all_proofs, args.batch))


if __name__ == '__main__':
    main()
