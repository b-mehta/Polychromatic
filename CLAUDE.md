# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formalization of polychromatic colourings of integers in Lean 4. A colouring of integers is *S*-polychromatic if every translate of set *S* contains an element of each colour class. The main theorem (`Lean/Polychromatic/Main.lean:final_result`) proves that every set of 4 integers admits a 3-polychromatic colouring.

**Primary language**: Lean 4 (`leanprover/lean4:v4.25.0-rc2`)
**Dependencies**: mathlib, subverso
**Website**: https://b-mehta.github.io/Polychromatic/

## Build Commands

All Lean commands run from the `Lean/` directory.

```bash
cd Lean
lake exe cache get        # REQUIRED before first build — downloads mathlib cache
lake build                # Build all proofs
lake build Polychromatic.Main  # Build a single module
lake clean                # Clean build artifacts
```

**Always run `lake exe cache get` before building.** Without it, mathlib builds from source (~60+ min). With cache, incremental builds take ~2–5 minutes.

### Other Components

- **Verso docs**: `cd Verso && lake exe docs` (uses Lean `v4.26.0-rc1` — different toolchain from main project, this is intentional). No `lake exe cache get` needed — just run `lake exe docs` directly. To generate highlighted Lean snippets first: `cd Lean && lake build :highlighted`.
- **API docs**: `cd Lean && ../scripts/build_docs.sh` — generates doc-gen4 HTML in `Lean/docbuild/.lake/build/doc`.
- **Jekyll site**: `cd site && bundle install && bundle exec jekyll serve` (Ruby 3.1+). Verso output goes into `site/_pages/`.
- **Generation**: C++ code in `Generation/` produces colouring log files consumed by `FourThree/Compute.lean`. Compile with `g++ -O3 -fopenmp coloring-integers.cpp -o coloring-integers`.

### Verso–Lean Integration

Lean code is pulled into the Verso site via `` ```anchor name (module := Module.Name) `` blocks, which reference `-- ANCHOR:` / `-- ANCHOR_END:` comments in the Lean source files. **Preserve these comments** — they mark sections extracted for website documentation.

## Architecture

### Lean Proofs (`Lean/Polychromatic/`)

| File | Purpose |
|------|---------|
| `Colouring.lean` | Core definitions: `IsPolychrom`, `HasPolychromColouring` |
| `PolychromNumber.lean` | `polychromNumber` — supremum of achievable colour counts |
| `Existence.lean` | Existence results via Lovász Local Lemma |
| `LocalLemma.lean` | Symmetric Lovász Local Lemma formalization |
| `LovaszFunction.lean` | Strauss function and asymptotics |
| `DiscreteProbability.lean` | Markov and Chebyshev inequalities |
| `Compactness.lean` | Rado selection principle, de Bruijn–Erdős theorem |
| `Main.lean` | Main theorem assembly: reduction chain → case split → computation |
| `ForMathlib/Misc.lean` | Lemmas targeted for upstream to mathlib |
| `FourThree/Theory.lean` | Defines `Accept` predicate and reduction lemmas (`suffices_*`) |
| `FourThree/FourThree.lean` | Mod-3 quick acceptance lemmas and metaprogramming infrastructure |
| `FourThree/Compute.lean` | Computational verification — `allC_289` via `prove_allC` tactic |
| `FourThree/Combi.lean` | Combinatorial case analysis for large cases |

### Main Theorem Proof Strategy (`Main.lean`)

The proof proceeds by successive reductions:
1. **`suffices_minimal`** — normalize to sets with minimal element 0
2. **`suffices_triple`** — check ordered triples 0 < a < b < c
3. **`suffices_flip`** — handle cases where a + b > c
4. **`suffices_gcd`** — reduce to coprime cases via scaling
5. **`suffices_cases`** — split: c < 289 (computational via `allC_289`) vs c ≥ 289 (combinatorial)

### Data Pipeline

```
Generation/coloring-integers.cpp   (C++, OpenMP)
        ↓
    temp-colors.log
        ↓
Generation/fill_in_blanks.py       (Python, Z3 solver)
        ↓
    full-colors.log
        ↓
FourThree/Compute.lean             (consumed by `prove_allC` tactic)
```

Python dependencies: `pip install -r requirements.txt` (z3-solver, tqdm).

## CI Pipeline

Defined in `.github/workflows/lean_action_ci.yml`. Triggers on push/PR to `main`.

| Job | What it does |
|-----|-------------|
| `make-docs` | Builds Lean proofs (with `mk_all-check`), generates doc-gen4 API docs |
| `run-verso` | Builds Lean, runs `lake build :highlighted`, then `lake exe docs` |
| `assemble` | Combines artifacts, builds Jekyll site |
| `deploy` | Deploys to GitHub Pages (main branch only) |

On push to `main`, CI also strips `-- ANCHOR:` comments and force-pushes clean code to the `release` branch.

## Lean Style Conventions

Configured in `lakefile.toml`:
- **`autoImplicit = false`** — all variables must be explicitly declared
- **`relaxedAutoImplicit = false`** — same, strictly enforced
- **Unicode function arrows** — use `fun a ↦ b` (not `=>`)
- **Line length limit** — 100 characters
- **No multiple active goals** — each tactic block targets one goal
- **mathlib standard lint set** — `weak.linter.mathlibStandardSet = true`

## Commit Conventions

- Author: Bhavik Mehta <b-mehta@users.noreply.github.com>
- Do not include Claude session URLs in commit messages
