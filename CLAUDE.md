# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formalization of polychromatic colourings of integers in Lean 4. A colouring of integers is *S*-polychromatic if every translate of set *S* contains an element of each colour class. The main theorem (`Lean/Polychromatic/Main.lean:final_result`) proves that every set of 4 integers admits a 3-polychromatic colouring.

## Build Commands

All Lean commands run from the `Lean/` directory.

```bash
cd Lean
lake exe cache get        # REQUIRED before first build — downloads mathlib cache
lake build                # Build all proofs
lake build Polychromatic.Main  # Build a single module
lake clean                # Clean build artifacts
```

**Always run `lake exe cache get` before building.** Without it, mathlib builds from source (~60+ min).

### Other Components

- **Verso docs**: `cd Verso && lake exe docs` (uses a different Lean toolchain — this is intentional)
- **Jekyll site**: `cd site && bundle exec jekyll serve` (Ruby 3.1+)
- **Generation**: C++ code in `Generation/` produces colouring log files consumed by `FourThree/Compute.lean`

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
| `FourThree/` | Four-colours-to-three reduction: `Theory.lean` (Accept predicate), `Compute.lean` (verification), `FourThree.lean` (case split), `Combi.lean` (case analysis) |

### Main Theorem Proof Strategy (`Main.lean`)

The proof proceeds by successive reductions:
1. **`suffices_minimal`** — normalize to sets with minimal element 0
2. **`suffices_triple`** — check ordered triples 0 < a < b < c
3. **`suffices_flip`** — handle cases where a + b > c
4. **`suffices_gcd`** — reduce to coprime cases via scaling
5. **`suffices_cases`** — split: c < 289 (combinatorial) vs c ≥ 289 (computational via `allC_289`)

### Data Pipeline

`Generation/coloring-integers.cpp` → `temp-colors.log` → `fill_in_blanks.py` (Z3) → `full-colors.log` → consumed by `FourThree/Compute.lean`

## Lean Style Conventions

Configured in `lakefile.toml`:
- **`autoImplicit = false`** — all variables must be explicitly declared
- **Unicode function arrows** — use `fun a ↦ b` (not `=>`)
- **Line length limit** — 100 characters
- **No multiple active goals** — each tactic block targets one goal
- **No rigid after flexible** — don't use `exact` after `simp`

Preserve `-- ANCHOR:` / `-- ANCHOR_END:` comments — they mark sections extracted for website documentation.

## Commit Conventions

- Author: Bhavik Mehta <b-mehta@users.noreply.github.com>
- Do not include Claude session URLs in commit messages
