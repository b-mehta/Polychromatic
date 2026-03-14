# Proof Simplification Tips

Patterns for shortening, simplifying, and deduplicating Lean proofs.

## General tactic reminders

- **`simp` with lemma lists** — a single `simp [h₁, h₂, h₃]` often replaces multiple `rw` steps. Use `simp only [...]` when `simp` is too aggressive or slow.
- **`gcongr`** handles monotonicity/congruence goals (e.g. `a ≤ b → f a ≤ f b`) — avoids manual `apply` chains.
- **`positivity`** closes positivity/nonnegativity goals automatically.
- **`field_simp`** clears denominators — combine with `ring` or `linarith` to finish.
- **`exact?` / `apply?` / `rw?`** — use these search tactics locally to find the right lemma, then inline the result.
- **`norm_num` extensions** — `norm_num [...]` can close goals involving specific numeric computations, including modular arithmetic.
- **`calc` blocks** — replace long `have` chains with `calc` when proving a sequence of inequalities or equalities.
- **`obtain ⟨a, b, h⟩ := ...`** — destructure in one step instead of separate `have` + `cases`.
- **`refine ... ?_`** — partially apply a lemma and let Lean generate remaining goals, avoiding verbose `apply` + `intro` sequences.
- **Combine `constructor` with `⟨..., ...⟩`** — use anonymous constructor syntax to close `And`/`Exists` goals concisely.
- **Merge `have`/`suffices` chains** — if a `have` is used exactly once right after, consider inlining it or using `suffices`.
- **Avoid redundant hypotheses** — if a lemma's hypothesis can be closed by `inferInstance` or `by omega`, remove the explicit `have` that provides it.

## grind subsumption

`grind` is powerful and often subsumes preceding tactics. When a proof ends with `tactic; grind`, try deleting the preceding tactic. Known results:
- **`rw [h]; grind`** → `grind` — works when `h` is a local hypothesis or a simple rewrite like `mul_add`/`mul_one`.
- **`congr 1; grind`** → `grind` — works for simple congruence goals.
- **`have := positivity_lemma; grind`** → `grind` — works when the positivity fact is inferrable.
- **`simp; grind`** → `grind` — works for simple normalization.
- **`simp [lemmas] <;> grind`** → `grind [lemmas]` — passing the simp lemmas directly to `grind` often works.
- **`simp [Fin.ext_iff] <;> omega`** → `grind [Fin.ext_iff]` — works for Fin equality/inequality goals with arithmetic.
- **`grind [mathlib_lemma]`** — passing a mathlib lemma (like `Nat.mod_add_div`) directly to grind works when grind needs the fact but can handle the surrounding commutativity/rearrangement.
- **`rw [ht]; omega`** → `grind` — when `ht` is a substitution like `g = 3*t`, grind handles the rewrite+arithmetic.
- Does NOT work when `rw` unfolds a local `have`-bound definition that `grind` can't see through.
- Does NOT work for `simp only [vadd_finset_insert, ...]; grind` — grind can't handle `vadd` on finsets without `simp` normalizing first.

## grind limitations

- `grind` CANNOT handle ZMod cast arithmetic with variable modulus. The ℕ-level reasoning works but ZMod-level casts are invisible to `grind`. Requires manual `Nat.cast` steps.
- `split_ifs <;> grind` fails for nested mod — grind can't handle `(v+3)%6` from hypothesis `v%6=0`.

## omega limitations

- `omega` treats variable multiplication as nonlinear — `g * (q + 1)` won't distribute. Fix: `rw [show g * (q + 1) = g * q + g from by ring]; omega`. Use `ring` to expand to a form where all multiplications have at least one literal operand.
- `set m := (expr).toNat` leaves an `if` in context that confuses `omega`. Use `by linarith` when an `(m : ℤ) = expr` hypothesis is available. Alternatively, need explicit positivity facts for omega to work.
- `omega` can fail at a call site due to many division/modular terms in context, even when it proves the same statement standalone. Fix with `change` to narrow the goal before `omega`. In particular, `Nat.div_add_mod` introduces both `/` and `%` terms — place it *after* any `omega` call that would choke on them.
- `omega` cannot prove `k = 0` from `A.length * h + (A.length + 1) * k = m` and `i < A.length * h` — this is nonlinear. Use `nlinarith` with relevant hypotheses instead.

## Deduplication strategies

- **`wlog` for symmetric cases** — when two branches of a case split have identical proof structure with swapped variables, `wlog h : P with H` followed by the symmetric case eliminates one branch entirely.
- **`suffices` to deduplicate symmetric case splits** — when a `by_cases` produces two branches with identical downstream proof structure, use `suffices ∃ ..., P ∧ Q` to extract the common proof, then have each branch only produce the witness.
- **Deduplicate `by_cases` with weaker intermediate goals** — when two branches prove slightly different intermediate types but share the same conclusion, hoist the conclusion to a `have ... by` block containing the `by_cases`, and use `omega` to bridge.
- **Extract repeated inline definitions** — when the same `let f := ...` appears in multiple helpers, extract it as a `private def`.
- **Parameterize repeated proof skeletons** — when multiple lemmas share the same skeleton differing only in a function and a coverage lemma, extract the skeleton into a helper parameterized by those differences.
- **Factor duplicated proof blocks** — look for identical multi-line blocks across branches and hoist shared proofs.
- **Check for existing lemmas before writing new ones** — search for an existing lemma with the same statement before writing a private helper. `Nat.Coprime a b` unfolds to `Nat.gcd a b = 1`, so lemmas taking one form accept the other.

## Inlining single-use private helpers

When a `private lemma` is used exactly once, inline it at the call site:
- Simple lemma proved by `omega`/`simp`/`grind`: replace call with inline `have ... := by omega`
- Destructuring result (`obtain ⟨k, hk⟩ := helper arg`): replace with `obtain ⟨k, hk⟩ : TargetType := by tactic`
- Lemma used as a term in `rw` or `exact`: replace with `have := ...; rw [this]`
- **Caveat**: `omega` and `grind` are context-sensitive. `grind [lemma]` can time out in large proof contexts — keep standalone lemmas when inlining causes timeouts.

## Golfing process (ordered by impact)

1. **Replace private helpers with mathlib lemmas** — use `lean_loogle` with the type signature to find exact matches.
2. **Derive lemmas from each other** — build on what's already proven nearby rather than reproving from scratch.
3. **Factor duplicated proof blocks** — look for identical multi-line blocks and hoist shared proofs.
4. **`lean_multi_attempt` for tactic replacement** — test 2–3 alternatives at once. Works well for single-tactic replacements. Does NOT work for replacing multi-line `have`/`calc` blocks.
5. **Remove unused parameters** — grep for `_h` prefix to find them quickly. After inlining a helper, check whether the inlined proof still needs all the enclosing lemma's parameters.
6. **Use the LSP, not `lake env lean`** — `lean_diagnostic_messages` is much faster for verifying individual edits than rebuilding the whole file.

## Nat.mod_mod_of_dvd for composite period proofs
`Nat.mod_mod_of_dvd p (dvd_mul_right a b)` proves `p % (a * b) % a = p % a`.
Replaces manual decomposition into quotient/remainder of the outer modulus.

## Deriving "zero remainder" from a general mod helper
Given `h : ∀ k a, (g * k + a) % d = a % d`, derive `∀ k, (g * k) % d = 0`
via `fun k => by simpa using h k 0`.

## Drop unnecessary type annotations

- **`(by grind : 0 < B.length)` → `(by grind)`** — Lean infers the expected type from the function argument position. Drop type ascriptions from `rw` arguments, function call arguments, and `grind`/`omega` hints.
- **`grind [mul_comm r h]`** — try dropping `mul_comm` hints; grind often handles commutativity itself.
- **`grind [gap_mod_cases_gen s j₀ jg 2 ...]` → `grind [gap_mod_cases_gen]`** — try the shortest form (just the lemma name) first; grind may find the right instantiation.
- **Extract hypotheses for grind** — if `grind [Nat.sub_add_cancel (by omega : 1 ≤ h)]` is needed, extract `have : 1 ≤ h := by omega` first so `grind [Nat.sub_add_cancel]` works.

## Successful golfing patterns (from Combi.lean)

- **`calc` → `rw + gcongr`** — a 2-step `calc` like `m = d * (m/d); _ ≤ d * 17 := by gcongr` becomes `rw [← Nat.mul_div_cancel' h]; gcongr`.
- **`calc` → `le_trans`** — `calc ep ≤ X; _ ≤ m` becomes `le_trans ep_le X_le` or `le_trans ... .le`.
- **Chained `rw`** — separate `have h1; rw [h1]; have h2; rw [h2]` collapses to `rw [h1, h2]` when the intermediate hypothesis isn't used elsewhere.
- **`Nat.pos_of_ne_zero (by intro h; simp [h] at hfoo)`** → `(by grind)` — grind derives positivity from `min ... > 1` directly.
- **Reuse nearby lemmas** — if a private lemma like `ZMod.val_add_one` exists locally, use it to shorten proofs of related results rather than reproving from `ZMod.val_add`.
- **Single-use `hΦ_cycle_shift`** — `fun x => by rw [hΦ_cycle, hα_ba, ← hΦ_cycle]` can be passed inline to `orbit_coloring_polychrom`.

## Formatting conventions

- **Don't join separate tactics with `;` in multi-line proofs** — in a proof that already spans multiple lines, `rw [...]; omega` at the end is an antipattern. Either make the entire proof a one-liner (if it fits under 100 chars), or keep each tactic on its own line. Exception: single-line proofs like `by rw [h]; omega` are fine.
- **Use the full 100-character line limit** — don't break lines at 80 characters when the project allows 100. Join continuation lines (`:=` assignments, `with` clauses, function arguments) onto the previous line whenever the result fits under 100 chars.
- **`grind [lemma.symm]` → `grind [lemma]`** — grind handles commutativity/symmetry internally, so `.symm` is usually unnecessary.

## Proof development process

- **Write a detailed informal proof before formalizing.** For any non-trivial goal (more than a single tactic), write out why the goal is true, what the key steps are, and what lemmas you expect to use. This prevents wasted cycles trying tactics blindly.
- **Fix errors in priority order**: syntax errors → type errors → unsolved goals/tactic failures → linter warnings. Lower-priority errors are often spurious when higher-priority ones exist.
- **Work on the hardest case first.** `sorry` the easy cases and focus on the hard one. If the hard case requires a different approach, effort on easy cases is wasted.
- **Fix errors iteratively, one at a time.** After each edit, check diagnostics before moving to the next error. Do not rewrite an entire file at once — changes interact in unexpected ways and make debugging harder.
