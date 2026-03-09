import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Coverage proof for `case_one_interval` (Combi.lean:687–763)

## Progress

**Lemmas 1-10**: All proven and moved to Combi.lean (5 commits on
`claude/theorem-1-case-1b-proof-0es7b`). The defs and sorry'd signatures
below (marked "STUBS") are duplicates needed for type-checking only.

**New helper lemmas** (marked "NEW WORK", all proven, compiling):
- `eqp_idx_succ_lt_m`: p+1 < m or eqp_idx(p+1) = s  ✓
- `non_straddle_witness`: non-straddle pair → witness d ∈ {0,1}  ✓
- `straddle_boundary_color`: straddle pair → F(p+1) = (j+1)%3  ✓
- `vg_mod_shift`: (v+(g+d))%m = ((v+g)%m + d)%m  ✓
- `gap2_jg_mod3`: gap=2 ∧ 3|s → (jg+1)%3 = j₀%3  ✓
- `gap1_j0_mod3`: gap=1 ∧ 3|s → (j₀+1)%3 = jg%3  ✓

**coverage_assembly**: TODO — the main assembly using the helpers above.

**Integration**: After coverage_assembly compiles, copy proof body into
Combi.lean:763 (the sorry in `case_one_interval`). Helper lemma calls work
directly since local `idx = eqp_idx q r` by definitional equality.

## Quick Start (for a fresh session)

**Goal**: Fill `coverage_assembly`, then integrate into `Combi.lean:763`.

**Recommended order** (hardest/riskiest first, to surface statement bugs early):

1. `straddle1_gap2` (Lemma 9) — hardest; case split on `j₀ + 1 < s` vs `= s`,
   then wrap/no-wrap subcases using `equiEndpoint` monotonicity. Most likely
   to reveal off-by-one issues in the statement.
2. `straddle2_gap1` (Lemma 10) — symmetric to 9; circular arc length ≥ 2q
3. `eqp_off_succ_same` (Lemma 4) — needs `mod_step` helper (see proof sketch below)
4. `eqp_off_succ_new` (Lemma 5) — needs `mod_zero_step` helper (see sketch below)
5. `eqp_idx_last` (Lemma 8) — division identity via `Nat.add_mul_div_right`
6. `compl_parity_witness` (Lemma 6) — pure `omega` after `Nat.mod_two_eq_zero_or_one`
7. `two_pairs_cover_split` (Lemma 7) — `omega` after `Nat.mod_lt` on both `j₁`, `j₂`
8. `coverage_assembly` — combine all above; see assembly pseudocode in Step 7

**Verification**: After `lake env lean Polychromatic/FourThree/Scratch1b4.lean`
passes with only `sorry` warnings, check `lake env lean Polychromatic/FourThree/Combi.lean`
to confirm integration works.

**Build commands** (from `Lean/` directory):
```
lake exe cache get                                    # first time only
lake env lean Polychromatic/FourThree/Scratch1b4.lean # check this file
lake env lean Polychromatic/FourThree/Combi.lean      # check integration
```

## Context: where this fits in the main theorem

The main theorem (`Main.lean:final_result`) proves every 4-element integer set
admits a 3-polychromatic colouring. After reductions, it splits:

```
final_result
 ├─ c < 289: computational (done, Compute.lean)
 └─ c ≥ 289: combinatorial
     ├─ Case 1: single-cycle regime (∃ s with 3∣s, g in middle range)
     │   ├─ Case 1a: done
     │   └─ Case 1b: case_one_interval ← THIS FILE fills its sorry
     └─ Case 2: done
```

`case_one_interval` (Combi.lean:687) constructs a 3-colouring of `ZMod m`
that is `{0, 1, g, g+1}`-polychromatic, given `3 ∣ s` and
`⌈m/s⌉ < g < 2⌊m/s⌋`. The colouring partitions `[0, m)` into `s`
near-equal intervals and assigns colour `(idx(p) + off(p) % 2) % 3`.

Lines 687–762 of Combi.lean are fully proven. The sorry at line 763 needs:
```
∃ a ∈ {0, 1, g, g+1}, c(v + a) = k.val
```
for arbitrary position `v` and target colour `k : Fin 3`.

## Integration plan (verified)

Apply `coverage_assembly` at Combi.lean:763 via `exact coverage_assembly ...`.
This is verified by `case_one_interval_test` at the bottom of this file:
- All hypotheses close with `rfl` (definitional equality) or `idx_in_interval'`
- The conclusion is definitionally equal to the goal (`exact hgoal`, no `convert`)
- Helper lemmas must be moved to Combi.lean (currently `private` in this file)

Alternative: copy the proof inline at the sorry site with `rfl` bridges.

## Sorry status

| # | Name | Deps | Difficulty | Strategy |
|---|------|------|------------|----------|
| 4 | `eqp_off_succ_same` | 3 | medium | `mod_step` helper + 4-way `split_ifs` |
| 5 | `eqp_off_succ_new` | 3 | medium | `mod_zero_step` helper + 4-way `split_ifs` |
| 6 | `compl_parity_witness` | — | easy | `omega` after `Nat.mod_two_eq_zero_or_one` |
| 7 | `two_pairs_cover_split` | — | easy | `omega` after `Nat.mod_lt` |
| 8 | `eqp_idx_last` | — | medium | `Nat.add_mul_div_right` or `Nat.div_eq_of_lt_le` |
| 9 | `straddle1_gap2` | — | hard | case split j₀+1<s vs =s, wrap/no-wrap |
| 10 | `straddle2_gap1` | — | hard | circular arc ≥ 2q contradicts g < 2q |
| — | `coverage_assembly` | 4–10 | medium | case split + witness construction |

Already proven: `eqp_idx_zero` (1), `eqp_off_zero` (2), `eqp_idx_step` (3),
`div_step`, `case_one_interval_test` (integration check).

## Key definitions

- `q = m / s`, `r = m % s` → `m = s * q + r`, `r < s`
- `bd = r * (q + 1)` — boundary between long (q+1) and short (q) intervals
- `eqp_idx q r p` = interval index of position `p`:
  `if p < bd then p / (q+1) else r + (p - bd) / q`
  (defeq to `let idx` in Combi.lean when `q = m/s`, `r = m%s`)
- `eqp_off q r p` = offset within interval:
  `if p < bd then p % (q+1) else (p - bd) % q`
- `c(p) = (eqp_idx q r (p%m) + eqp_off q r (p%m) % 2) % 3`
- `equiEndpoint m s j = q*j + min(r, j)` — start of interval `j`
  - `equiEndpoint(0) = 0`, `equiEndpoint(s) = m`
  - interval `j` = `[equiEndpoint(j), equiEndpoint(j+1))`
  - length = `if j < r then q+1 else q`

## Hypotheses at the sorry site (Combi.lean:763)

```
s g m : ℕ,  hs : 0 < s,  hs3 : 3 ∣ s
h_lb : (m + s - 1) / s < g,  h_ub : g < 2 * (m / s)
q := m / s,  r := m % s,  bd := r * (q + 1)
hm_eq : m = s * q + r,  hr_lt : r < s,  hq_pos : 0 < q
hs_le : s ≤ m,  hg1_lt_m : g + 1 < m,  hs3_le : 3 ≤ s
v : ℕ (= n.val),  hv_lt : v < m,  k : Fin 3
j₀ := idx v,  jg := idx ((v + g) % m)   -- via set
hgap : (jg + s - j₀) % s = 1 ∨ ... = 2
hidx_lt : ∀ p, p < m → idx p < s
hj₀_lt : j₀ < s,  hjg_lt : jg < s
hphase : j₀ % 3 ≠ jg % 3
hc_phase : ∀ p, c p = idx(p%m) % 3 ∨ c p = (idx(p%m)+1) % 3
-- NOT available (must derive): interval membership for v, (v+g)%m
```

## General arithmetic helpers

**div_step** (proven): For `b > 0`: `(a+1)/b = a/b ∨ (a+1)/b = a/b+1`.
Proof: `a/b ≤ (a+1)/b` (monotonicity) and `(a+1)/b ≤ a/b + 1`
(since `a + 1 ≤ b*(a/b+1)` using `Nat.div_add_mod`).

**mod_step** (needed for Lemma 4): If `b > 0` and `a/b = (a+1)/b`,
then `(a+1) % b = a % b + 1`.
Proof: From `Nat.div_add_mod`: `b*(a/b) + a%b = a` and
`b*((a+1)/b) + (a+1)%b = a+1`. Since the quotients are equal,
the `b*(·)` terms cancel: `(a+1)%b - a%b = 1`, i.e.,
`(a+1) % b = a % b + 1`. (In ℕ, `(a+1)%b ≥ a%b` follows from
the equation and `(a+1)%b ≥ 0`.)

**mod_zero_step** (needed for Lemma 5): If `b > 0` and
`(a+1)/b = a/b + 1`, then `(a+1) % b = 0`.
Proof: From `Nat.div_add_mod`: `b*(a/b) + a%b = a` and
`b*(a/b+1) + (a+1)%b = a+1`. Expanding: `b*a/b + b + (a+1)%b
= b*a/b + a%b + 1`. So `b + (a+1)%b = a%b + 1`. Since
`a%b < b` (Nat.mod_lt), we have `a%b + 1 ≤ b`. Since
`(a+1)%b ≥ 0`, we need `b ≤ a%b + 1 ≤ b`, forcing
`a%b = b - 1` and `(a+1)%b = 0`.

## Step 1 — Lemma 7: two pairs with different phases cover all 3

For `j₁ % 3 ≠ j₂ % 3` and `k < 3`: `k ∈ {j₁%3, (j₁+1)%3}` or
`k ∈ {j₂%3, (j₂+1)%3}`.

Proof: The pair `{j%3, (j+1)%3}` covers exactly 2 of {0,1,2}.
Two such pairs with *different* base residues cover all 3.
Exhaust `j₁%3 ∈ {0,1,2}`, `j₂%3 ∈ {0,1,2}\{j₁%3}`,
`k ∈ {0,1,2}`: all 18 cases check out. (omega/decide in Lean.)

## Step 2 — Lemmas 3,4,5: consecutive position analysis

**Lemma 3** (eqp_idx_step, proven): `idx(p+1) = idx(p)` or `idx(p)+1`.
Four cases from `split_ifs` on `p+1 < bd` and `p < bd`:
1. Both `< bd`: apply `div_step` with divisor `q+1`. ✓
2. `p+1 < bd`, `p ≥ bd`: impossible (`omega`). ✓
3. `p+1 ≥ bd`, `p < bd` (cross-branch): `p+1 = bd = r*(q+1)`.
   So `(p+1)/(q+1) = r` and `p/(q+1) = r-1` (since `p = r*(q+1)-1
   = (r-1)*(q+1) + q`). And `idx(p+1) = r + 0 = r = (r-1)+1
   = idx(p)+1`. ✓
4. Both `≥ bd`: rewrite `p+1-bd = (p-bd)+1`, apply `div_step`
   with divisor `q`. ✓

**Lemma 4** (eqp_off_succ_same): If `idx(p+1) = idx(p)`, then
`off(p+1) = off(p) + 1`.
Proof structure: `unfold eqp_off; split_ifs` (same 4 cases).
1. Both `< bd`: From `h : idx(p+1) = idx(p)` and both in first
   branch, `p/(q+1) = (p+1)/(q+1)`. Apply `mod_step`. ✓
2. `p+1 < bd`, `p ≥ bd`: impossible (`omega`). ✓
3. Cross-branch: `idx(p+1) = idx(p) + 1` (from Lemma 3 cross case),
   contradicting `h : idx(p+1) = idx(p)`. Derive `False` by
   showing `idx(p+1) ≠ idx(p)` in this branch. Concretely:
   `unfold eqp_idx at h; split_ifs at h` produces `r + 0 = p/(q+1)`,
   but `p/(q+1) = r - 1` (from `p < r*(q+1)`), giving `r = r-1`.
   Since `r > 0` (from `p ≥ 0` and `p < r*(q+1)`): contradiction. ✓
4. Both `≥ bd`: From `h` in second branch, `(p-bd)/q = (p+1-bd)/q`.
   Rewrite `p+1-bd = (p-bd)+1`, apply `mod_step`. ✓

**Lemma 5** (eqp_off_succ_new): If `idx(p+1) ≠ idx(p)`, then
`off(p+1) = 0`.
Proof structure: same 4-way `split_ifs`.
1. Both `< bd`: From `h : idx(p+1) ≠ idx(p)` and both in first
   branch, `(p+1)/(q+1) ≠ p/(q+1)`. By `div_step`, `(p+1)/(q+1)
   = p/(q+1) + 1`. Apply `mod_zero_step`: `(p+1)%(q+1) = 0`. ✓
2. Impossible: `omega`. ✓
3. Cross-branch: `p+1 = bd`. `off(p+1) = (p+1 - bd) % q
   = 0 % q = 0`. ✓
4. Both `≥ bd`: From `h`, `(p+1-bd)/q ≠ (p-bd)/q`. Rewrite
   `p+1-bd = (p-bd)+1`. By `div_step`, quotient increased by 1.
   Apply `mod_zero_step`: `((p-bd)+1) % q = 0`. ✓

## Step 3 — Lemma 6: complementary parity coverage

Given `j` and `a`, the pair `{(j + a%2) % 3, (j + (a+1)%2) % 3}`
equals `{j%3, (j+1)%3}`.

Proof: `a%2 ∈ {0, 1}`.
- If `a%2 = 0`: `(a+1)%2 = 1`. Pair = `{(j+0)%3, (j+1)%3}` =
  `{j%3, (j+1)%3}`. ✓
- If `a%2 = 1`: `(a+1)%2 = 0`. Pair = `{(j+1)%3, (j+0)%3}` =
  `{(j+1)%3, j%3}`. ✓

So for any target `t ∈ {j%3, (j+1)%3}`, one of the two
expressions equals `t`. (omega/decide after `Nat.mod_two_eq_zero_or_one`.)

## Step 4 — Lemma 8: idx(m-1) = s-1

Given `m = s*q + r`, `r < s`, `q ≥ 1`, `s ≥ 1`.

First: `m - 1 ≥ bd = r*(q+1)`.
`m - 1 - bd = s*q + r - 1 - r*q - r = (s-r)*q - 1`.
Since `s > r` and `q ≥ 1`: `(s-r)*q ≥ 1`, so `m-1 ≥ bd`. ✓

So `idx(m-1) = r + (m - 1 - bd) / q = r + ((s-r)*q - 1) / q`.

Write `(s-r)*q - 1 = (s-r-1)*q + (q-1)`. Since `q-1 < q`:
`((s-r-1)*q + (q-1)) / q = s-r-1` (by `Nat.add_mul_div_right`
applied to `(q-1) + (s-r-1)*q`).

So `idx(m-1) = r + (s - r - 1) = s - 1`. ✓

Lean proof strategy: `unfold eqp_idx; split_ifs; simp/omega`
after providing the key division identity via
`Nat.add_mul_div_right` or `Nat.div_eq_of_lt_le`.

## Step 5 — Lemma 9: Pair 1 straddle → gap = 2

**Hypotheses**:
- `hstrad : equiEndpoint(j₀+1) ≤ v + 1` (pair (v,v+1) straddles)
- `hv_hi : v < equiEndpoint(j₀+1)`
- Combined: `v + 1 = equiEndpoint(j₀+1)`, i.e., `v` is the last
  element of interval `j₀`.
- `hgap : gap ∈ {1, 2}` where `gap = (jg + s - j₀) % s`

**Goal**: `gap = 2`, i.e., rule out `gap = 1`.

Assume for contradiction `gap = 1`, i.e., `jg = (j₀+1) % s`.

Since `v = equiEndpoint(j₀+1) - 1`:
  `v + g = equiEndpoint(j₀+1) - 1 + g`.

**Key bound**: Every interval has length ≤ `⌈m/s⌉ < g`.
In particular, `equiEndpoint(j+1) - equiEndpoint(j) ≤ q+1
≤ (m+s-1)/s < g` for all `j`.

**Case A: j₀ + 1 < s** (so `(j₀+1)%s = j₀+1`):

Since `g > equiEndpoint(j₀+2) - equiEndpoint(j₀+1)`:
  `v + g = equiEndpoint(j₀+1) - 1 + g ≥ equiEndpoint(j₀+2)`.

Sub-case A1 (`v + g < m`, non-wrapping):
  `(v+g)%m = v + g ≥ equiEndpoint(j₀+2)`.
  But for `jg = j₀+1`: `(v+g)%m < equiEndpoint(j₀+2)` (from
  `hvg_hi`). Contradiction. ✓

Sub-case A2 (`v + g ≥ m`, wrapping):
  `(v+g)%m = v + g - m`. For `jg = j₀+1`: need
  `equiEndpoint(j₀+1) ≤ v + g - m`, i.e.,
  `g ≥ m + 1` (since `v = equiEndpoint(j₀+1) - 1`).
  But `g < 2q ≤ 2*(m/3) ≤ 2m/3 < m` (since `m ≥ s ≥ 3`).
  So `g < m < m + 1`. Contradiction. ✓

**Case B: j₀ + 1 = s** (so `j₀ = s-1`, `(j₀+1)%s = 0`):

`v = equiEndpoint(s) - 1 = m - 1`. So `v + g = m - 1 + g`.
Since `g ≥ 1`: `v + g ≥ m`, so wrapping: `(v+g)%m = g - 1`.

For `gap = 1`: `jg = 0`. Need `g - 1 < equiEndpoint(1)`.
`equiEndpoint(1) = q + min(r, 1)`.

- If `r = 0`: `⌈m/s⌉ = q`. So `g > q`, `g ≥ q + 1`,
  `g - 1 ≥ q = equiEndpoint(1)`. But need `g-1 < equiEndpoint(1)`.
  Contradiction. ✓
- If `r > 0`: `⌈m/s⌉ = q + 1`. So `g > q + 1`, `g ≥ q + 2`,
  `g - 1 ≥ q + 1 = equiEndpoint(1)`. Contradiction. ✓

## Step 6 — Lemma 10: Pair 2 straddle → gap = 1

**Hypotheses**:
- `hstrad : equiEndpoint(jg+1) ≤ (v+g)%m + 1`
- `hvg_hi : (v+g)%m < equiEndpoint(jg+1)`
- Combined: `(v+g)%m = equiEndpoint(jg+1) - 1`, i.e., `(v+g)%m`
  is the last element of interval `jg`.
- `hv_hi : v < equiEndpoint(j₀+1)`

**Goal**: `gap = 1`, i.e., rule out `gap = 2`.

Assume for contradiction `gap = 2`.

**Key idea**: The circular arc from `equiEndpoint(j₀+1)` to
`equiEndpoint(jg+1)` contains exactly `gap = 2` intervals, each
of length ≥ `q`. So the arc length ≥ `2q`. And `g ≥` arc length
(since `v ≤ equiEndpoint(j₀+1) - 1` and `(v+g)%m =
equiEndpoint(jg+1) - 1`). So `g ≥ 2q`, contradicting `g < 2q`.

**Detailed computation**:

`(v+g)%m = equiEndpoint(jg+1) - 1` and `v ≤ equiEndpoint(j₀+1) - 1`.

Non-wrapping (`v + g < m`):
  `v + g = equiEndpoint(jg+1) - 1`.
  `g = v + g - v ≥ equiEndpoint(jg+1) - equiEndpoint(j₀+1)`.

  For `gap = 2`: `jg = (j₀+2) % s`. When non-wrapping and
  `jg ≥ j₀` (so `jg = j₀+2 < s`):
  `equiEndpoint(j₀+3) - equiEndpoint(j₀+1)` = sum of lengths of
  intervals `j₀+1` and `j₀+2`, each ≥ `q`. So `g ≥ 2q`.
  But `g < 2q`. Contradiction. ✓

  When `jg < j₀` (wrapping gap): non-wrapping is impossible
  because `(v+g)%m = v+g` is in interval `jg` which ends before
  interval `j₀` starts, so `v+g < equiEndpoint(jg+1) ≤
  equiEndpoint(j₀) ≤ v`, impossible since `g > 0`. ✓

Wrapping (`v + g ≥ m`):
  `v + g = m + equiEndpoint(jg+1) - 1` (since `(v+g)%m =
  v + g - m = equiEndpoint(jg+1) - 1`).
  `g = m + equiEndpoint(jg+1) - 1 - v
     ≥ m + equiEndpoint(jg+1) - equiEndpoint(j₀+1)`.

  The circular arc length from `equiEndpoint(j₀+1)` to
  `equiEndpoint(jg+1)` (going forward through `m`) is:
  `m - equiEndpoint(j₀+1) + equiEndpoint(jg+1)` = sum of
  interval lengths from `j₀+1` through `jg` (mod `s`), which
  is 2 intervals for `gap = 2`, each of length ≥ `q`.
  So `g ≥ 2q`. But `g < 2q`. Contradiction. ✓

  Sub-cases for `jg = (j₀+2) % s`:
  - `j₀ = s-2, jg = 0`: arc = `(m - equiEndpoint(s-1))
    + equiEndpoint(1)` = lengths of intervals `s-1` and `0`,
    each ≥ `q`. ✓
  - `j₀ = s-1, jg = 1`: arc = `(m - equiEndpoint(s))
    + equiEndpoint(2)` = `equiEndpoint(2) ≥ 2q`. ✓
  - `j₀+2 < s` (wrapping due to `v+g ≥ m`):
    `g ≥ m + equiEndpoint(j₀+3) - equiEndpoint(j₀+1) ≥ m + 2q
    > 2q`. ✓

## Step 7 — Main assembly in case_one_interval

**Given**: `v < m`, `j₀ = idx(v)`, `jg = idx((v+g)%m)`,
`j₀ % 3 ≠ jg % 3`, `gap ∈ {1,2}`, `3 ∣ s`.

**Straddling definitions**:
- Pair 1 (v, v+1) straddles iff `idx(v+1) ≠ idx(v)`,
  equivalently `equiEndpoint(j₀+1) ≤ v + 1` (v is last in j₀).
- Pair 2 ((v+g)%m, (v+g+1)%m) straddles iff
  `idx(((v+g)%m)+1) ≠ idx((v+g)%m)`, equivalently
  `equiEndpoint(jg+1) ≤ (v+g)%m + 1`.

Note: at most one pair can straddle. If pair 1 straddles then
`gap = 2` (Lemma 9), and if pair 2 straddles then `gap = 1`
(Lemma 10). Since gap can't be both 1 and 2, at most one does.

**Coloring values**:
- `c(p) = (idx(p%m) + off(p%m) % 2) % 3`.
- Non-straddling pair `(p, p+1)` in interval `j`: By Lemma 4,
  `off(p+1) = off(p) + 1`. So `{c(p), c(p+1)} =
  {(j + off(p)%2)%3, (j + (off(p)+1)%2)%3} = {j%3, (j+1)%3}`
  (by Lemma 6). Witness for any `t ∈ {j%3, (j+1)%3}` exists.
- Straddling pair `(p, p+1)`: By Lemma 5, `off(p+1) = 0`.
  So `c(p+1) = (idx(p+1) + 0) % 3 = idx(p+1) % 3`.
  Since `idx(p+1) = idx(p) + 1 = j + 1`: `c(p+1) = (j+1) % 3`.
  And when `j+1 = s` (wrap): `(v+1)%m = 0`, `idx(0) = 0`,
  `c(v+1) = 0 % 3 = 0 = s % 3 = (j+1) % 3` (since `3 ∣ s`).

**Case split** (by Lemma 7, `k` is in pair 1 or pair 2's range):

1. **k ∈ {j₀%3, (j₀+1)%3}** — need witness `a ∈ {0, 1}`:
   - Pair 1 non-straddling: Lemma 6 gives
     `c(v) = k` or `c(v+1) = k`. Use `a = 0` or `a = 1`. ✓
   - Pair 1 straddling: `c(v+1) = (j₀+1)%3`. If `k = (j₀+1)%3`:
     use `a = 1`. If `k = j₀%3`: need witness from pair 2
     (see case 3 below). ✓

2. **k ∈ {jg%3, (jg+1)%3}** — need witness `a ∈ {g, g+1}`:
   - Pair 2 non-straddling: Lemma 6 gives `c(v+g) = k` or
     `c(v+g+1) = k`. Use `a = g` or `a = g+1`. ✓
   - Pair 2 straddling: `c(v+g+1) = (jg+1)%3`. If
     `k = (jg+1)%3`: use `a = g+1`. If `k = jg%3`: need
     witness from pair 1 (see case 3 below). ✓

3. **Both pairs have the needed color** — when one pair straddles:
   - Pair 1 straddles → `gap = 2` (Lemma 9).
     `{jg%3, (jg+1)%3} = {(j₀+2)%3, (j₀+3)%3} = {(j₀+2)%3, j₀%3}`.
     So `j₀%3 ∈ {jg%3, (jg+1)%3}`. Pair 2 is non-straddling
     (since pair 1 straddles), so Lemma 6 gives a witness for
     `j₀%3` from pair 2. Combined with `c(v+1) = (j₀+1)%3`
     from the straddle, all 3 colors are covered. ✓
   - Pair 2 straddles → `gap = 1` (Lemma 10).
     `{j₀%3, (j₀+1)%3}` already covers `jg%3 = (j₀+1)%3`.
     Pair 1 is non-straddling, so Lemma 6 gives a witness for
     `jg%3` from pair 1. Combined with `c(v+g+1) = (jg+1)%3
     = (j₀+2)%3`, all 3 colors are covered. ✓

## Sub-goal mapping (from Combi.lean TODO)

**(a)** Non-straddling pair covers both phases → Lemmas 4 + 6.
**(b)** Straddling pair produces boundary color `(j+1)%3` → Lemmas 3 + 5.
**(c)** At most one pair straddles → Lemmas 9 + 10.
**(d)** Gap determines pair 2's color set → (a) + (c).

## Bridge (item 5): `eqp_idx`/`eqp_off` ↔ local `let` bindings

The sorry site uses `let idx`, `let off`, `let c` which are
definitionally equal to `eqp_idx q r`, `eqp_off q r`, and the
coloring formula. Connect via `have : eqp_idx q r p = idx p := rfl`.

## Assembly pseudocode (item 6)

```
rcases two_pairs_cover_split j₀ jg hphase k.val k.isLt with hk1 | hk2
· -- k ∈ {j₀%3, (j₀+1)%3}
  by_cases hstrad1 : idx((v+1)%m) = idx(v%m)
  · -- Non-straddling: (a) gives witness from pair 1
  · -- Straddling: (b) gives (j₀+1)%3; (c)→gap=2→(d) gives j₀%3 from pair 2
· -- k ∈ {jg%3, (jg+1)%3} — symmetric
```

## Execution order

1. Lemmas 9, 10 (straddle → gap, hardest — surface statement bugs early)
2. mod_step, mod_zero_step helpers + Lemmas 4, 5
3. Lemma 8 (idx of last element)
4. Lemmas 6, 7 (easy arithmetic, no deps)
5. Bridge layer
6. Assembly at Combi.lean:763
-/

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║ STUBS: already proven in Combi.lean (sorry here = placeholder) ║
-- ╚══════════════════════════════════════════════════════════════════╝

private def eqp_idx (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p / (q + 1)
  else r + (p - r * (q + 1)) / q

private def eqp_off (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p % (q + 1)
  else (p - r * (q + 1)) % q

private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) :
    eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by sorry

private lemma eqp_idx_m (q r s : ℕ) (hq : 0 < q) (hr : r < s)
    (_hs : 0 < s) :
    eqp_idx q r (s * q + r) = s := by sorry

private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by sorry

private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p + 1) :
    eqp_off q r (p + 1) = 0 := by sorry

private lemma compl_parity_witness (j a : ℕ) (t : ℕ)
    (ht : t < 3)
    (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    (j + a % 2) % 3 = t ∨ (j + (a + 1) % 2) % 3 = t := by sorry

private lemma two_pairs_cover_split (j₁ j₂ : ℕ)
    (hne : j₁ % 3 ≠ j₂ % 3)
    (t : ℕ) (ht : t < 3) :
    (t = j₁ % 3 ∨ t = (j₁ + 1) % 3) ∨
    (t = j₂ % 3 ∨ t = (j₂ + 1) % 3) := by sorry

open Finpartition in
private lemma straddle1_gap2 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (q : ℕ) (hq : q = m / s)
    (r : ℕ) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (v : ℕ) (hv : v < m)
    (j₀ jg : ℕ)
    (hj₀ : j₀ = eqp_idx q r v) (hjg : jg = eqp_idx q r ((v + g) % m))
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hstrad : eqp_idx q r (v + 1) = eqp_idx q r v + 1)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 2 := by sorry

open Finpartition in
private lemma straddle2_gap1 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (q : ℕ) (hq : q = m / s)
    (r : ℕ) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (v : ℕ) (hv : v < m)
    (j₀ jg : ℕ)
    (hj₀ : j₀ = eqp_idx q r v) (hjg : jg = eqp_idx q r ((v + g) % m))
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hstrad : eqp_idx q r (((v + g) % m) + 1) =
      eqp_idx q r ((v + g) % m) + 1)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 1 := by sorry

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║ NEW WORK: helpers + assembly that need real proofs             ║
-- ╚══════════════════════════════════════════════════════════════════╝

/-! ### Assembly lemma: coverage proof for `case_one_interval`

This is the main goal at Combi.lean:763. Given the equi-partition setup
(q, r, bd, idx, off, c) and the established facts (hphase, hgap, hidx_lt,
hc_phase), we produce a witness `a ∈ {0, 1, g, g+1}` with `c(v+a) = k`.

The proof uses:
- `two_pairs_cover_split` (Lemma 7) to split into pair 1 or pair 2
- `compl_parity_witness` (Lemma 6) for non-straddling pairs
- `eqp_off_succ_same` (Lemma 4) / `eqp_off_succ_new` (Lemma 5) for
  offset analysis at straddle boundaries
- `straddle1_gap2` (Lemma 9) / `straddle2_gap1` (Lemma 10) for the
  at-most-one-straddle argument
- `idx_in_interval'` (from Combi.lean) for interval membership

The `c` function is `(eqp_idx q r (p%m) + eqp_off q r (p%m) % 2) % 3`.

**Integration plan**: This lemma is NOT meant to be applied directly at the
sorry site via `exact coverage_assembly ...`. Instead, the *proof* of this
lemma will be copied into `case_one_interval` at line 763, replacing the
sorry. The sorry site already has `c`, `idx`, `off`, `j₀`, `jg` as local
definitions that are definitionally equal to `eqp_idx`/`eqp_off`-based
versions. The proof will use helper lemmas from this file (Lemmas 4–10)
via `have : eqp_idx q r p = idx p := rfl`-style bridges, or by directly
unfolding `eqp_idx`/`eqp_off` since they are defeq to the local `let`s.

## Proof plan for `coverage_assembly`

**Goal**: Given color `k : Fin 3`, find `a ∈ {0, 1, g, g+1}` such that
`(eqp_idx q r ((v+a) % m) + eqp_off q r ((v+a) % m) % 2) % 3 = k`.

Write `F(p) = (eqp_idx q r (p%m) + eqp_off q r (p%m) % 2) % 3` for the
coloring function. We have two "pairs":
- Pair 1: positions `v` and `v+1` (offsets a=0, a=1)
- Pair 2: positions `v+g` and `v+g+1` (offsets a=g, a=g+1)

Each pair `{p, p+1}` lies in interval `j` or straddles `j/(j+1)`:
- **Non-straddling** (eqp_idx(p+1) = eqp_idx(p)):
  Consecutive offsets have different parities, so `{F(p), F(p+1)} = {j%3, (j+1)%3}`.
  → `compl_parity_witness` gives the right offset d ∈ {0,1} for any target in this set.
- **Straddling** (eqp_idx(p+1) = eqp_idx(p) + 1):
  `eqp_off(p+1) = 0`, so `F(p+1) = (j+1) % 3`. And `F(p) = (j + off(p)%2) % 3`,
  which is either `j%3` or `(j+1)%3` depending on parity.

**Step 1** (`two_pairs_cover_split`): Since `j₀ % 3 ≠ jg % 3` and `3 | s`,
every `k < 3` is in `{j₀%3, (j₀+1)%3}` or `{jg%3, (jg+1)%3}`.
→ Case split: pair 1 covers k, or pair 2 covers k.

**Step 2** (`eqp_idx_step`): For each pair, case split on straddle vs non-straddle.

**Step 3** (Non-straddle cases): Use `compl_parity_witness` to find the witness.
- Pair 1 non-straddle: witness d ∈ {0,1}, directly gives a ∈ {0,1} ⊂ {0,1,g,g+1}.
- Pair 2 non-straddle: witness d ∈ {0,1}, maps to a ∈ {g, g+1} ⊂ {0,1,g,g+1}.
  Need: `(v+(g+d)) % m = (vg+d) % m` (where `vg = (v+g)%m`).
  For d=0: trivial (`(v+g)%m = vg`).
  For d=1: `(v+g+1)%m = (vg+1)%m` by `Nat.add_mod`.

**Step 4** (Straddle cases): When one pair straddles, use the OTHER pair.
- Pair 1 straddles → `straddle1_gap2` → gap = 2 → `(jg+1)%3 = j₀%3`.
  - If k = (j₀+1)%3: witness is a=1 directly. Need `F(v+1) = (j₀+1)%3`.
    By `eqp_off_succ_new`, off(v+1) = 0, so `F(v+1) = (j₀+1+0)%3`.
    Edge case: if v+1=m, then `(v+1)%m = 0`, `eqp_idx(0)=0`, `eqp_off(0)=0`,
    and `(j₀+1)%3 = s%3 = 0` (since 3|s and j₀=s-1). Still works.
  - If k = j₀%3: pair 2 must be non-straddling (else `straddle2_gap1` → gap=1,
    contradicting gap=2). Use pair 2 with target k = j₀%3 = (jg+1)%3.
- Pair 2 straddles → `straddle2_gap1` → gap = 1 → `j₀%3 = (jg+1)%3`.
  Symmetric to above with roles swapped.

## Helper lemmas for the proof

The proof body is complex (4-way case split × sub-cases). To keep it manageable,
we factor out these helpers:

1. `non_straddle_witness`: If eqp_idx doesn't step at p, and k is in
   {j%3, (j+1)%3}, produce d ∈ {0,1} with F(p+d) = k. Needs p+1 < m.

2. `p_succ_lt_m`: If eqp_idx(p+1) = eqp_idx(p) (or = eqp_idx(p)+1 with
   eqp_idx(p)+1 < s), then p+1 < m. Proof: if p+1=m then eqp_idx(m)=s,
   but eqp_idx(p) < s.

3. `straddle_boundary_color`: If eqp_idx(p+1) = j+1 (straddle), then
   F(p+1) = (j+1)%3, handling both p+1 < m and p+1 = m edge cases.

4. `vg_mod_shift`: `(v + (g + d)) % m = ((v+g)%m + d) % m` for d ∈ {0,1}.

5. `gap2_jg_mod3`: If gap=2 and 3|s, then (jg+1)%3 = j₀%3.

6. `gap1_j0_mod3`: If gap=1 and 3|s, then (j₀+1)%3 = jg%3.
-/
/-! #### Helper 1: p+1 < m when eqp_idx doesn't jump to s -/
private lemma eqp_idx_succ_lt_m (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s) (hs : 0 < s)
    (hm_eq : m = s * q + r)
    (hp : p < m) (hidx_lt : eqp_idx q r p < s) :
    p + 1 < m ∨ eqp_idx q r (p + 1) = s := by
  by_cases h : p + 1 < m
  · exact Or.inl h
  · have hpm : p + 1 = m := by omega
    right
    rw [hpm, hm_eq]
    exact eqp_idx_m q r s hq_pos hr_lt hs

/-! #### Helper 2: non-straddle witness

If eqp_idx doesn't step at p, and target k is in {j%3, (j+1)%3},
produce d ∈ {0,1} with the coloring formula at (p+d)%m equaling k. -/
private lemma non_straddle_witness (q r p : ℕ)
    (hq_pos : 0 < q)
    (hp : p < m) (hp1 : p + 1 < m)
    (hsame : eqp_idx q r (p + 1) = eqp_idx q r p)
    (j : ℕ) (hj : j = eqp_idx q r p)
    (t : ℕ) (ht : t < 3) (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    ∃ d ∈ ({0, 1} : Finset ℕ),
      (eqp_idx q r ((p + d) % m) +
        eqp_off q r ((p + d) % m) % 2) % 3 = t := by
  have hoff := eqp_off_succ_same q r p hq_pos hsame
  rcases compl_parity_witness j (eqp_off q r p) t ht hpair with h | h
  · exact ⟨0, by simp, by
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hp, ← hj]
      exact h⟩
  · exact ⟨1, by simp, by
      rw [Nat.mod_eq_of_lt hp1, hsame, ← hj, hoff]
      exact h⟩

/-! #### Helper 3: straddle boundary color

When eqp_idx steps at p, the coloring at p+1 gives (j+1)%3,
handling the edge case p+1 = m (wraps to 0). -/
private lemma straddle_boundary_color (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s) (hs : 0 < s)
    (hs3 : 3 ∣ s)
    (hm_eq : m = s * q + r)
    (hp : p < m)
    (hstep : eqp_idx q r (p + 1) = eqp_idx q r p + 1)
    (j : ℕ) (hj : j = eqp_idx q r p) (hj_lt : j < s) :
    (eqp_idx q r ((p + 1) % m) +
      eqp_off q r ((p + 1) % m) % 2) % 3 = (j + 1) % 3 := by
  by_cases h : p + 1 < m
  · -- Normal case: p + 1 < m
    rw [Nat.mod_eq_of_lt h]
    have hoff := eqp_off_succ_new q r p hq_pos hstep
    rw [hstep, ← hj, hoff]
  · -- Wrap case: p + 1 = m
    have hpm : p + 1 = m := by omega
    rw [hpm, Nat.mod_self]
    have hidx0 : eqp_idx q r 0 = 0 := by
      simp [eqp_idx]
    have hoff0 : eqp_off q r 0 = 0 := by
      simp [eqp_off]
    rw [hidx0, hoff0]
    -- Need: 0 = (j + 1) % 3. Since eqp_idx(m) = s = j+1 and 3 | s.
    rw [hpm] at hstep
    have hm_idx : eqp_idx q r m = s := by
      rw [hm_eq]; exact eqp_idx_m q r s hq_pos hr_lt hs
    have hjs : j + 1 = s := by rw [hj]; omega
    obtain ⟨d3, hd3⟩ := hs3; omega

/-! #### Helper 4: modular shift for vg

`(v + (g + d)) % m = ((v + g) % m + d) % m` -/
private lemma vg_mod_shift (v g d : ℕ) (hm : 0 < m) :
    (v + (g + d)) % m = ((v + g) % m + d) % m := by
  have h1 := Nat.add_mod (v + g) d m
  have h2 := Nat.add_mod ((v + g) % m) d m
  rw [Nat.mod_mod_of_dvd _ (dvd_refl m)] at h2
  rw [show v + (g + d) = (v + g) + d from by ring, h1, h2]

/-! #### Helper 5: gap=2 implies (jg+1)%3 = j₀%3 -/
private lemma gap2_jg_mod3 (s j₀ jg : ℕ) (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap2 : (jg + s - j₀) % s = 2) :
    (jg + 1) % 3 = j₀ % 3 := by
  obtain ⟨d3, hd3⟩ := hs3
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  have : (jg + s - j₀) / s ≤ 1 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < s)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h
  · rw [h] at hdiv; omega
  · have : (jg + s - j₀) / s = 1 := by omega
    rw [this] at hdiv; omega

/-! #### Helper 6: gap=1 implies (j₀+1)%3 = jg%3 -/
private lemma gap1_j0_mod3 (s j₀ jg : ℕ) (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap1 : (jg + s - j₀) % s = 1) :
    (j₀ + 1) % 3 = jg % 3 := by
  obtain ⟨d3, hd3⟩ := hs3
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  have : (jg + s - j₀) / s ≤ 1 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < s)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h
  · rw [h] at hdiv; omega
  · have : (jg + s - j₀) / s = 1 := by omega
    rw [this] at hdiv; omega

/-! #### Main assembly -/
open Finpartition in
private lemma coverage_assembly (s g m q r : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs3_le : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (hg1_lt_m : g + 1 < m)
    (hq : q = m / s) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (hm_eq : m = s * q + r)
    (v : ℕ) (hv : v < m) (k : Fin 3)
    (j₀ : ℕ) (hj₀_def : j₀ = eqp_idx q r v)
    (jg : ℕ) (hjg_def : jg = eqp_idx q r ((v + g) % m))
    (hphase : j₀ % 3 ≠ jg % 3)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1)) :
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      (eqp_idx q r ((v + a) % m) +
        eqp_off q r ((v + a) % m) % 2) % 3 = k.val := by
  sorry

/-! ### Verification: check coverage_assembly fills the sorry in case_one_interval

We copy `case_one_interval` with sorry'd stubs for its private dependencies,
and verify that `coverage_assembly` (also sorry'd) can close the goal. -/
section Verification

-- Stubs for private lemmas from Combi.lean
private lemma lift_coloring_witness_stub {m g : ℕ} [NeZero m]
    [Fact (1 < m)] (hg_lt : g + 1 < m)
    {c : ℕ → ℕ} (hc_lt : ∀ p, c p < 3)
    (hc_period : ∀ p, c (p % m) = c p)
    {n : ZMod m} {k : Fin 3}
    (h : ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      c (n.val + a) = k.val) :
    ∃ s ∈ ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
      Finset (ZMod m)),
      (⟨c (n + s).val, hc_lt _⟩ : Fin 3) = k := by sorry

private lemma gap_bound_interval_stub (s g m : ℕ) (hs : 0 < s)
    (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) :
    let bd := (m % s) * (m / s + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (m / s + 1)
      else m % s + (p - bd) / (m / s)
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2 := by
  sorry

private lemma phase_ne_of_gap_stub {s j₀ jg : ℕ} (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨
      (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by sorry

open Finpartition in
private lemma idx_in_interval_stub (s m : ℕ)
    (hs : 0 < s) (hs_le : s ≤ m) (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1)
      else r + (p - bd) / q
    j < s ∧ equiEndpoint m s j ≤ p ∧
    p < equiEndpoint m s (j + 1) := by sorry

-- Full copy of case_one_interval with the sorry replaced by
-- coverage_assembly application
open Finpartition in
private lemma case_one_interval_test (m : ℕ)
    (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  set q := m / s
  set r := m % s
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hr_lt : r < s := Nat.mod_lt m hs
  have hq_pos : 0 < q := by
    have : q * s ≤ m := Nat.div_mul_le_self m s
    have : q ≤ (m + s - 1) / s := by
      rw [Nat.le_div_iff_mul_le hs]; omega
    omega
  have hs_le : s ≤ m := by
    nlinarith [Nat.div_mul_le_self m s]
  have hg1_lt_m : g + 1 < m := by
    nlinarith [Nat.div_mul_le_self m s, Nat.le_of_dvd hs hs3]
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  set bd := r * (q + 1)
  let idx (p : ℕ) : ℕ :=
    if p < bd then p / (q + 1) else r + (p - bd) / q
  let off (p : ℕ) : ℕ :=
    if p < bd then p % (q + 1) else (p - bd) % q
  let c (p : ℕ) : ℕ :=
    (idx (p % m) + off (p % m) % 2) % 3
  have hc_lt3 : ∀ p, c p < 3 :=
    fun p => Nat.mod_lt _ (by omega)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c]
    rw [Nat.mod_mod_of_dvd p (dvd_refl m)]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness_stub hg1_lt_m hc_lt3 hc_period ?_⟩
  set v := n.val
  have hv_lt : v < m := ZMod.val_lt n
  have hc_phase : ∀ p, c p = idx (p % m) % 3 ∨
      c p = (idx (p % m) + 1) % 3 := by
    intro p; simp only [c]
    have : off (p % m) % 2 = 0 ∨ off (p % m) % 2 = 1 :=
      by omega
    rcases this with h | h <;> simp [h] <;> omega
  set j₀ := idx v with hj₀_def
  set jg := idx ((v + g) % m) with hjg_def
  have hs3_le : 3 ≤ s := Nat.le_of_dvd hs hs3
  have hgap := gap_bound_interval_stub s g m hs hs3_le hs_le
    h_lb h_ub v hv_lt
  have hidx_lt : ∀ p, p < m → idx p < s := by
    intro p hp; simp only [idx]; split
    · have : p / (q + 1) < r := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)]
        exact ‹_›
      omega
    · rename_i hge; push_neg at hge
      have : (p - bd) / q < s - r := by
        rw [Nat.div_lt_iff_lt_mul hq_pos]
        have : r * (q + 1) + (s - r) * q = s * q + r := by
          have : (s - r) * q + r * q = s * q := by
            rw [← Nat.add_mul,
              Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
          linarith
        omega
      omega
  have hj₀_lt : j₀ < s := hidx_lt v hv_lt
  have hjg_lt : jg < s :=
    hidx_lt ((v + g) % m) (Nat.mod_lt _ (by omega))
  have hphase : j₀ % 3 ≠ jg % 3 :=
    phase_ne_of_gap_stub hs3 hj₀_lt hjg_lt hgap
  -- === HERE: the sorry site ===
  -- Goal: ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = k.val
  -- Derive interval membership from idx_in_interval_stub
  have hiv := idx_in_interval_stub s m hs hs_le v hv_lt
  have hivg := idx_in_interval_stub s m hs hs_le
    ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Bridge: show the goal matches coverage_assembly's conclusion
  have hgoal := coverage_assembly s g m q r
    hs hs3 hs3_le hs_le h_lb h_ub hg1_lt_m
    rfl rfl hq_pos hr_lt hm_eq
    v hv_lt k
    j₀ rfl jg rfl
    hphase hgap hj₀_lt hjg_lt
    hiv.2.1 hiv.2.2 hivg.2.1 hivg.2.2
  exact hgoal

end Verification
