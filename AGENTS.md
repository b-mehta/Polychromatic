# AGENTS.md

Instructions for AI coding agents working on this repository.

## Project Overview

Formalization of polychromatic colourings of integers in Lean 4. A colouring of integers is *S*-polychromatic if every translate of set *S* contains an element of each colour class. The main theorem (`Lean/Polychromatic/Main.lean:final_result`) states that every set of 4 integers admits a 3-polychromatic colouring. The proof is complete modulo the computational verification in `FourThree/Compute.lean` (temporarily `sorry`'d to check CI).

**Primary Language**: Lean 4 (formal proof)
**Supporting Languages**: C++, Python, Ruby/Jekyll

## Repository Structure

```
Generation/             # C++ & Python code to generate explicit colourings
Lean/                   # Lean 4 formal proofs (main project)
Verso/                  # Website generation from Lean documentation
site/                   # Jekyll website source
```

Lean and Verso use **different Lean toolchains** (check their respective `lean-toolchain` files) — this is intentional.

## Build Commands

All Lean commands run from the `Lean/` directory.

```bash
cd Lean
lake exe cache get        # REQUIRED before first build — downloads mathlib cache
lake build                # Build all proofs
lake build Polychromatic.Main  # Build a single module
lake env lean Polychromatic/FourThree/Combi.lean  # Fast single-file check (no linking)
```

**Always run `lake exe cache get` before building.** Without it, mathlib builds from source (~60+ min). With cache, incremental builds take ~2–5 minutes.

### Other Components

- **Verso docs**: `cd Verso && lake exe docs` (requires the Lean build to have completed first). The docs build shells out to `../Lean` to run `subverso-extract-mod` using the Lean project's toolchain. Lean code is pulled into the site via fenced `anchor` code blocks (e.g. ````anchor name (module := Module.Name)````), which reference `-- ANCHOR:` / `-- ANCHOR_END:` comments in the Lean source files.
- **Jekyll site**: `cd site && bundle exec jekyll serve` (Ruby 3.1+)
- **Generation**: C++ code in `Generation/` produces colouring log files consumed by `FourThree/Compute.lean`
- **API docs**: `cd Lean && ../scripts/build_docs.sh`

### Quick Reference

```bash
cd Lean && lake exe cache get && lake build   # Full build from scratch
cd Lean && lake build                         # Incremental build
cd Verso && lake exe docs                     # Generate documentation
cd site && bundle exec jekyll serve           # Serve website locally
cd Lean && lake clean                         # Clean Lean build
```

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

## Continuous Integration

**File**: `.github/workflows/lean_action_ci.yml`
**Triggers**: Push to `main`, pull requests to `main`, manual dispatch

The CI pipeline builds Lean (using `lean-action`, which handles `lake exe cache get` automatically), runs Verso, builds the Jekyll site, and deploys to GitHub Pages. On push to `main`, it also cleans `-- ANCHOR:` annotations and force-pushes clean code to the `release` branch.

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

## Making Changes

### Modifying Lean Proofs

1. Edit `.lean` files in `Lean/Polychromatic/`
2. Build to verify: `cd Lean && lake build`
3. **Do not** remove `-- ANCHOR:` comments — they're used for documentation extraction

### Modifying Website Content

1. Edit Lean documentation in `Verso/PolychromaticSite/`
2. Regenerate: `cd Verso && lake exe docs`
3. Build site: `cd site && bundle exec jekyll build`

## Common Pitfalls

- **Long build times**: Forgot to run `lake exe cache get` before building
- **Different Lean versions**: Verso and main Lean use different toolchains — this is intentional, don't try to unify them
- **`lake update` changes toolchain**: `lake update subverso` often modifies `lean-toolchain` — always revert this

## Commit Conventions

- Do not include AI session URLs in commit messages
