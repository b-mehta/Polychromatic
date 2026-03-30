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
- **`by_contra!`** — combines `by_contra` + `push_neg` in one step. Replaces the verbose `by_contra h; push_neg at h` pattern.
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
- **`grind [lemma.symm]` → `grind [lemma]`** — grind handles commutativity/symmetry internally, so `.symm` is usually unnecessary.
- Does NOT work for `simp only [vadd_finset_insert, ...]; grind` — grind can't handle `vadd` on finsets without `simp` normalizing first.

## grind limitations

- `grind` CANNOT handle ZMod cast arithmetic with variable modulus. The ℕ-level reasoning works but ZMod-level casts are invisible to `grind`. Requires manual `Nat.cast` steps.

## omega limitations

Prefer `grind` or `lia` over `omega` — they handle more cases, especially nonlinear arithmetic and division/modular terms.

## Deduplication strategies

- **`wlog` for symmetric cases** — when two branches of a case split have identical proof structure with swapped variables, `wlog h : P with H` followed by the symmetric case eliminates one branch entirely.
- **`suffices` to deduplicate symmetric case splits** — when a `by_cases` produces two branches with identical downstream proof structure, use `suffices ∃ ..., P ∧ Q` to extract the common proof, then have each branch only produce the witness.
- **Deduplicate `by_cases` with weaker intermediate goals** — when two branches prove slightly different intermediate types but share the same conclusion, hoist the conclusion to a `have ... by` block containing the `by_cases`, and use `grind` or `lia` to bridge.
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
6. **Verify incrementally** — check each edit individually rather than rebuilding the whole file.

## Nat.mod_mod_of_dvd for composite period proofs
`Nat.mod_mod_of_dvd p (dvd_mul_right a b)` proves `p % (a * b) % a = p % a`.
Replaces manual decomposition into quotient/remainder of the outer modulus.

## Deriving "zero remainder" from a general mod helper
Given `h : ∀ k a, (g * k + a) % d = a % d`, derive `∀ k, (g * k) % d = 0`
via `fun k => by simpa using h k 0`.

## Successful golfing patterns (from Combi.lean)

- **`calc` → `rw + gcongr`** — a 2-step `calc` like `m = d * (m/d); _ ≤ d * 17 := by gcongr` becomes `rw [← Nat.mul_div_cancel' h]; gcongr`.
- **`calc` → `le_trans`** — `calc ep ≤ X; _ ≤ m` becomes `le_trans ep_le X_le` or `le_trans ... .le`.
- **Chained `rw`** — separate `have h1; rw [h1]; have h2; rw [h2]` collapses to `rw [h1, h2]` when the intermediate hypothesis isn't used elsewhere.
- **Consecutive `rw` on same target** — `rw [a]; rw [b]` → `rw [a, b]`, and `rw [x] at h; rw [y] at h` → `rw [x, y] at h`. Only combine when both are at the same indent level and rewrite the same target (goal or same hypothesis).
- **`Nat.pos_of_ne_zero (by intro h; simp [h] at hfoo)`** → `(by grind)` — grind derives positivity from `min ... > 1` directly.
- **Reuse nearby lemmas** — if a private lemma like `ZMod.val_add_one` exists locally, use it to shorten proofs of related results rather than reproving from `ZMod.val_add`.
- **Single-use `hΦ_cycle_shift`** — `fun x => by rw [hΦ_cycle, hα_ba, ← hΦ_cycle]` can be passed inline to `orbit_coloring_polychrom`.

## Formatting conventions

- **Don't join separate tactics with `;` in multi-line proofs** — in a proof that already spans multiple lines, `rw [...]; omega` at the end is an antipattern. Either make the entire proof a one-liner (if it fits under 100 chars), or keep each tactic on its own line. Exception: single-line proofs like `by rw [h]; omega` are fine.
- **Use the full 100-character line limit** — don't break lines at 80 characters when the project allows 100. Join continuation lines (`:=` assignments, `with` clauses, function arguments) onto the previous line whenever the result fits under 100 chars.

## Golfing workflow

- **Try `grind` with lemma hints.** Many multi-line proofs that manually case-split and chain `have` statements can be closed by a single `grind [relevant_lemma₁, relevant_lemma₂]`. Key hints to try: `Nat.div_add_mod`, `Nat.mul_add_mod`, `Nat.sub_add_cancel`, `equiEndpoint_monotone`, `Finset.card_pair`, `Finset.card_le_three`.
- **`rw [...] at ...; omega` compression.** In contradiction proofs with wrap/no-wrap subcases, replace 3-4 line blocks (`have : (v+g)%m = v+g := ...; rw [...] at ...; omega`) with a single line: `rw [Nat.mod_eq_of_lt h] at hvg_hi; omega`.
- **`simp + grind` for Finset cardinality contradictions.** Instead of explicit `have hsub : S ⊆ T; grind [card_le_card hsub, card_le_three]`, try `simp only [h] at hcard; grind [Finset.card_pair]`.
- **`calc` one-liners for bound chains.** Replace `have h1 := ...; have h2 := ...; omega` with `calc x < y := ...; _ ≤ z := ...` or `le_trans ... ...`.
- **Use `grind` not `omega` for equiEndpoint.** `grind` handles `j+1+1` vs `j+2` normalisation that `omega` can't, especially with `grind [equiEndpoint_monotone]`.

## Finding simplifications systematically

### High-impact structural changes
- **Inline nearly-identical lemmas into a single dispatch.** When 3+ lemmas share the same structure (e.g., `obtain ⟨u, hu⟩; rw [...]`) differing only in case-specific data, merge them into one proof with `rcases` dispatch. Factor common setup before the dispatch, and extract shared sub-computations as local `have` helpers. This was the single biggest win (6 `case_one_res_*` → 1 `case_one_residues`, ~55 lines saved).
- **Remove single-use private helpers.** `grep` for each private lemma name; if it appears exactly twice (definition + one call), inline at the call site. But verify the proof still closes — `grind`/`omega` are context-sensitive and may need the old intermediate `have`s.
- **Remove unused parameters.** After golfing, check `lean_diagnostic_messages` for "unused variable" warnings and remove the parameter + all caller arguments. `Nat.succ_div`-based proofs often make `hb : 0 < b` unnecessary.

### Medium-impact tactic patterns
- **`simp only [def, h₁, h₂] at h` to inline unfold+rw.** Instead of `unfold foo; rw [if_pos h1]; rw [if_neg h2]`, use `simp only [foo, h1, h2] at h`. This was very effective for `eqp_idx`/`eqp_off` case analysis.
- **`refine ⟨..., ?_, ?_⟩ <;> grind [def, key_fact]`** to close multiple structurally similar goals at once. Works when the goals differ only in index values and `grind` can handle both.
- **`<;> [left; right] <;> rw [h, ...]`** to compress symmetric disjunction dispatches. When `rcases` gives two branches that both end with `left; exact ...` / `right; exact ...` using the same tactic chain, combine with `<;>`.
- **`grind [local_helper arg1 arg2]`** to skip intermediate `have` + `rw` steps. If a proof is `have : v + g = g * (q+1) + r := by grind; rw [this, color_at ...]`, try `grind [color_at (q+1) r hr_lt]` directly. This gives `grind` the rewrite target as a hint so it can compute the full chain. Works best when the `have` is simple arithmetic and the rewrite target is a function application.
- **`Nat.succ_div` for division step lemmas.** `grind [Nat.succ_div]` subsumes `(a+1)/b = a/b` or `= a/b + 1` proofs. Also `rw [← Nat.dvd_iff_mod_eq_zero]; by_contra hdvd; simp [Nat.succ_div, hdvd] at h` for remainder-resets-to-zero proofs.
- **`Nat.add_mod_left` not `Nat.add_mod_right`** for `(s + k) % s = k % s`. `Nat.add_mod_right` matches `(a + b) % b` (modulus is second addend), `Nat.add_mod_left` matches `(a + b) % a` (modulus is first addend).

### Low-impact but reliable
- **Remove duplicate `open Foo in` lines.** These accumulate during refactoring.
- **Remove consecutive blank lines.** Keep exactly one between declarations.
- **Join single-tactic `by` blocks** where the `have` declaration + body fits under 100 chars: `have foo : T := by grind` instead of splitting across two lines.

## Proof development process

- **Write a detailed informal proof before formalizing.** For any non-trivial goal (more than a single tactic), write out why the goal is true, what the key steps are, and what lemmas you expect to use. This prevents wasted cycles trying tactics blindly.
- **Fix errors in priority order**: syntax errors → type errors → unsolved goals/tactic failures → linter warnings. Lower-priority errors are often spurious when higher-priority ones exist.
- **Work on the hardest case first.** `sorry` the easy cases and focus on the hard one. If the hard case requires a different approach, effort on easy cases is wasted.
- **Fix errors iteratively, one at a time.** After each edit, check diagnostics before moving to the next error. Do not rewrite an entire file at once — changes interact in unexpected ways and make debugging harder.
