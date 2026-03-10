# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

See also:
- **`.claude/simplification-patterns.md`** — read when golfing, simplifying, or writing proofs
- **`.claude/combi-patterns.md`** — read when working on `FourThree/Combi.lean` (block colorings, ZMod arithmetic, proof patterns)

## Project Overview

Formalization of polychromatic colourings of integers in Lean 4. A colouring of integers is *S*-polychromatic if every translate of set *S* contains an element of each colour class. The main theorem (`Lean/Polychromatic/Main.lean:final_result`) proves that every set of 4 integers admits a 3-polychromatic colouring.

## Build Commands

All Lean commands run from the `Lean/` directory.

```bash
cd Lean
lake exe cache get        # REQUIRED before first build — downloads mathlib cache
lake build                # Build all proofs
lake build Polychromatic.Main  # Build a single module
lake env lean Polychromatic/FourThree/Combi.lean  # Fast single-file check (no linking)
```

**Always run `lake exe cache get` before building.** Without it, mathlib builds from source (~60+ min).

### Other Components

- **Verso docs**: `cd Verso && lake exe docs` (requires the Lean build above to have completed first). The Verso project uses a different Lean toolchain — this is intentional. The docs build shells out to `../Lean` to run `subverso-extract-mod` using the Lean project's toolchain. Lean code is pulled into the site via `` ```anchor name (module := Module.Name) `` blocks, which reference `-- ANCHOR:` / `-- ANCHOR_END:` comments in the Lean source files.
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
5. **`suffices_cases`** — split: c < 289 (computational via `allC_289`) vs c ≥ 289 (combinatorial)

### Data Pipeline

`Generation/coloring-integers.cpp` → `temp-colors.log` → `fill_in_blanks.py` (Z3) → `full-colors.log` → consumed by `FourThree/Compute.lean`

## SubVerso Dependency Management

Both `Lean/` and `Verso/` depend on [SubVerso](https://github.com/leanprover/subverso) and **must use the same commit hash**. The difference is the branch prefix:

- **`Lean/lakefile.toml`**: `rev = "no-modules/<hash>"` — uses the `no-modules` branch (non-module oleans, for projects without Lean's module system)
- **`Verso/lakefile.toml`**: `rev = "<hash>"` — uses the `main` branch (module oleans, required by Verso)

When updating SubVerso, keep these constraints in mind:

1. **Same commit hash in both projects.** The `no-modules` branch mirrors `main` with auto-generated demodulized versions. Both branches share commit hashes for most of the history.
2. **The SubVerso version must compile with both the Lean and Verso toolchains.** The Verso docs build invokes `subverso-extract-mod` against `../Lean` using the Lean project's toolchain.
3. **`lake update subverso` often changes `lean-toolchain` — always revert this.** The toolchains for both projects are intentionally pinned and should not change as a side effect.
4. **Check API compatibility with Verso.** Newer SubVerso versions may change types (e.g., `Token.Kind.const` gained an extra parameter in commit `61d4c9d`). The pinned Verso version must match the SubVerso API.

## Lean Style Conventions

Configured in `lakefile.toml`:
- **`autoImplicit = false`** — all variables must be explicitly declared
- **Unicode function arrows** — use `fun a ↦ b` (not `=>`)
- **Line length limit** — 100 characters
- **No multiple active goals** — each tactic block targets one goal
- **No rigid after flexible** — don't use `exact` after `simp`

Preserve `-- ANCHOR:` / `-- ANCHOR_END:` comments — they mark sections extracted for website documentation.

### Antipatterns

- **Avoid `show`** — use `have` to prove intermediate facts and `change` to adjust the goal type. `show` is less readable and mixes poorly with other tactics:
  ```lean
  -- Bad: show as inline proof term
  rcases show d = 0 ∨ d = 1 ∨ d = 2 from by grind with h | h | h
  -- Good: extract to have
  have : d = 0 ∨ d = 1 ∨ d = 2 := by grind
  rcases this with h | h | h

  -- Bad: show inside rw
  rw [hpm, Nat.mod_self, show eqp_idx q r 0 = 0 from by simp [eqp_idx]]
  -- Good: extract to have, then rw
  have : eqp_idx q r 0 = 0 := by simp [eqp_idx]
  rw [hpm, Nat.mod_self, this]

  -- Bad: show to change goal type
  show ((h * q' + r') % h % 3 + ...) % 3 = _
  -- Good: use change instead
  change ((h * q' + r') % h % 3 + ...) % 3 = _
  ```

## Proof Development Workflow Tips

- **Develop in a scratch file, then integrate** — for complex sorry-filling work, create a temporary `ScratchXxx.lean` that imports the target module. Prove all helper lemmas there first, verify they compile, then move them into the real file in dependency order (leaves first). Delete the scratch file once integration is complete.
- **Move lemmas bottom-up** — when integrating from scratch to target, move dependency-free helpers first, then lemmas that depend on them. This ensures each intermediate state compiles. Commit after each batch of moves.
- **`omega` handles most ℕ modular arithmetic goals** — lemmas about `(a + s - b) % s` with bounds `a < s`, `b < s` are typically closed by `omega` after case-splitting on `Nat.div_add_mod` and bounding the quotient. The pattern: `have hdiv := Nat.div_add_mod (x + s - y) s; have : (x + s - y) / s ≤ 1 := by rw [Nat.div_le_iff_le_mul ...]; omega; rcases ... with h | h; omega; omega`.
- **`nlinarith` for nonlinear ℕ bounds** — goals like `¬(s * q + r < r * (q + 1))` where the negation involves products of variables are handled by `nlinarith`, not `omega`.
- **Boundary wrap pattern** — when a proof needs `p + 1 < m` but `p + 1` might equal `m`, use `by_cases h : p + 1 < m` then handle the wrap case `p + 1 = m` (where `(p+1) % m = 0`) separately. Factor this into a helper like `eqp_idx_succ_lt_m` that returns `p + 1 < m ∨ <boundary condition>`.
- **Coverage proofs via `rcases` dispatch** — for showing "every color `k : Fin 3` is hit", the pattern is: (1) prove two pairs of indices cover all 3 colors via `two_pairs_cover_split`, (2) `rcases` on which pair covers `k`, (3) for each pair, `rcases` on straddle vs non-straddle (`eqp_idx_step`), (4) in each branch produce a witness `⟨d, hd_mem, hd_eq⟩`.
- **`suffices` for symmetric straddle/non-straddle branches** — when a straddle case and non-straddle case for pair 2 both need to produce a witness of the same type, use `suffices ∃ d, ...` to share the downstream proof structure.
- **Keep helper lemma signatures minimal** — pass only what's needed. For instance, `non_straddle_witness` takes the raw `eqp_idx` equality rather than the full interval structure — this makes it reusable across both pairs.


## Commit Conventions

- Do not include Claude session URLs in commit messages
