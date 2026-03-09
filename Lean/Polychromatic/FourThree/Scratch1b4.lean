import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Scratch file 4: coverage proof helpers for case_one_interval

## Definitions

- `q = m / s`, `r = m % s`, so `m = s * q + r` and `r < s`
- `bd = r * (q + 1)` (boundary between long and short intervals)
- `idx(p) = if p < bd then p / (q + 1) else r + (p - bd) / q`
- `off(p) = if p < bd then p % (q + 1) else (p - bd) % q`
- `c(p) = (idx(p % m) + off(p % m) % 2) % 3`
- `equiEndpoint m s i = m / s * i + min(m % s, i) = q * i + min(r, i)`
- Interval `j` is `[equiEndpoint(j), equiEndpoint(j+1))`
- `equiEndpoint(0) = 0`, `equiEndpoint(s) = m` (by `equiEndpoint_hi`)
- Interval length: `equiEndpoint(j+1) - equiEndpoint(j) = if j < r then q+1 else q`
  (by `card_of_mem_equipartitionToIco_parts_aux`)
- Hence every interval has length ≥ q and ≤ q+1 ≤ ⌈m/s⌉

## Goal

We need: `∃ a ∈ {0, 1, g, g+1}, c(v + a) = k.val`, where `k : Fin 3`.

**Known context**: `j₀ = idx(v)`, `jg = idx((v + g) % m)`,
`j₀ % 3 ≠ jg % 3`, `gap := (jg + s - j₀) % s ∈ {1, 2}`,
`3 ∣ s`, `g > ⌈m/s⌉ = (m + s - 1) / s`, `g < 2 * (m / s) = 2q`.

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

1. Lemmas 6, 7 (easy arithmetic, no deps)
2. mod_step, mod_zero_step helpers + Lemmas 4, 5
3. Lemma 8 (idx of last element)
4. Lemmas 9, 10 (straddle → gap, hardest)
5. Bridge layer
6. Assembly at Combi.lean:763
-/

-- Equi-partition index: which interval does position p fall in?
private def eqp_idx (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p / (q + 1)
  else r + (p - r * (q + 1)) / q

-- Equi-partition offset: position within the interval
private def eqp_off (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p % (q + 1)
  else (p - r * (q + 1)) % q

/-! ### Lemma 1: idx at 0 is 0

Proof: 0 < r*(q+1) iff r > 0.
If r > 0: 0 < r*(q+1), so idx(0) = 0/(q+1) = 0.
If r = 0: r*(q+1) = 0, so ¬(0 < 0), idx(0) = 0 + (0-0)/q = 0.
In both cases: 0. -/
private lemma eqp_idx_zero (q r : ℕ) :
    eqp_idx q r 0 = 0 := by
  simp [eqp_idx]

/-! ### Lemma 2: off at 0 is 0

Proof: Same case split as Lemma 1.
If r > 0: off(0) = 0 % (q+1) = 0.
If r = 0: off(0) = (0-0) % q = 0 % q = 0. -/
private lemma eqp_off_zero (q r : ℕ) :
    eqp_off q r 0 = 0 := by
  simp [eqp_off]

/-! ### Lemma 3: consecutive idx values differ by 0 or 1

Proof by case split on the branch of the if-then-else for p
and p+1.

Case 1: p < bd and p+1 < bd (both in first branch).
  idx(p) = p/(q+1), idx(p+1) = (p+1)/(q+1).
  General fact: for any a,b with b>0, a/b and (a+1)/b differ
  by 0 or 1. (Because (a+1) = a + 1, and the quotient can
  increase by at most 1 when the input increases by 1.)

Case 2: p ≥ bd and p+1 ≥ bd (both in second branch).
  idx(p) = r + (p-bd)/q, idx(p+1) = r + (p+1-bd)/q.
  Same general fact: (p-bd)/q and (p+1-bd)/q differ by 0 or 1.
  So idx values differ by 0 or 1.

Case 3: p < bd and p+1 ≥ bd (cross-branch).
  p = bd - 1. idx(p) = (bd-1)/(q+1).
  bd = r*(q+1), so (bd-1)/(q+1) = (r*(q+1)-1)/(q+1).
  Since r*(q+1)-1 = (r-1)*(q+1) + q, the quotient is r-1.
  idx(p+1) = r + (p+1-bd)/q = r + 0/q = r.
  r = (r-1) + 1 = idx(p) + 1. ✓

Case 4: p ≥ bd and p+1 < bd. Impossible since p < p+1. -/
-- General fact: consecutive ℕ quotients differ by 0 or 1
private lemma div_step (a b : ℕ) (hb : 0 < b) :
    (a + 1) / b = a / b ∨ (a + 1) / b = a / b + 1 := by
  have hle : a / b ≤ (a + 1) / b :=
    Nat.div_le_div_right (Nat.le_succ a)
  suffices h : (a + 1) / b ≤ a / b + 1 by omega
  have h1 := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  have hring : b * (a / b + 1) = b * (a / b) + b := by ring
  have hub : a + 1 ≤ b * (a / b + 1) := by linarith
  calc (a + 1) / b
      ≤ b * (a / b + 1) / b := Nat.div_le_div_right hub
    _ = a / b + 1 := Nat.mul_div_cancel_left _ hb

private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) :
    eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by
  unfold eqp_idx
  split_ifs with h1 h2
  · -- p+1 < r*(q+1), p < r*(q+1): both in first branch
    exact div_step p (q + 1) (by omega)
  · -- p+1 < r*(q+1), p ≥ r*(q+1): impossible
    omega
  · -- p+1 ≥ r*(q+1), p < r*(q+1): cross branch, p+1 = r*(q+1)
    right
    have hpeq : p + 1 = r * (q + 1) := by omega
    have hr_pos : 0 < r := by nlinarith
    have h_succ : (p + 1) / (q + 1) = r := by
      rw [hpeq]; exact Nat.mul_div_cancel r (by omega)
    have hne : p / (q + 1) ≠ r := by
      intro heq
      have := Nat.div_mul_le_self p (q + 1)
      rw [heq] at this; linarith
    have hidx_p : p / (q + 1) = r - 1 := by
      have := div_step p (q + 1) (by omega); omega
    rw [hpeq, Nat.sub_self, Nat.zero_div, hidx_p]; omega
  · -- p+1 ≥ r*(q+1), p ≥ r*(q+1): both in second branch
    have hsub :
        p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by
      omega
    rw [hsub]
    have := div_step (p - r * (q + 1)) q hq; omega

/-! ### Lemma 4: same idx → off increases by 1

Uses general helper `mod_step`: if `b > 0` and `a/b = (a+1)/b`,
then `(a+1) % b = a % b + 1`. (See top-level proof sketch.)

`unfold eqp_off; split_ifs` (same 4 cases as Lemma 3):
1. Both `< bd`: `h` gives `p/(q+1) = (p+1)/(q+1)`.
   Apply `mod_step`: `(p+1)%(q+1) = p%(q+1) + 1`. ✓
2. `p+1 < bd`, `p ≥ bd`: impossible (`omega`). ✓
3. Cross-branch: contradicts `h`. In this branch,
   `idx(p+1) = r ≠ r-1 = idx(p)` (from Lemma 3 analysis),
   but `h` says they're equal. Derive `False` via
   `unfold eqp_idx at h; split_ifs at h`. ✓
4. Both `≥ bd`: `h` gives `(p-bd)/q = (p+1-bd)/q`.
   Rewrite `p+1-bd = (p-bd)+1`, apply `mod_step`. ✓ -/
private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by
  sorry

/-! ### Lemma 5: different idx → off is 0

Uses general helper `mod_zero_step`: if `b > 0` and
`(a+1)/b = a/b + 1`, then `(a+1) % b = 0`.
(See top-level proof sketch for derivation.)

`unfold eqp_off; split_ifs` (same 4 cases):
1. Both `< bd`: `h` gives `(p+1)/(q+1) ≠ p/(q+1)`.
   By `div_step`, `(p+1)/(q+1) = p/(q+1) + 1`.
   Apply `mod_zero_step`: `(p+1)%(q+1) = 0`. ✓
2. Impossible: `omega`. ✓
3. Cross-branch: `p+1 = bd`. Goal: `(p+1 - bd) % q = 0`.
   `p+1 - bd = 0`, `0 % q = 0`. ✓
4. Both `≥ bd`: `h` gives `(p+1-bd)/q ≠ (p-bd)/q`.
   Rewrite `p+1-bd = (p-bd)+1`. By `div_step`, quotient
   increased by 1. Apply `mod_zero_step`: `((p-bd)+1)%q = 0`. ✓ -/
private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) ≠ eqp_idx q r p) :
    eqp_off q r (p + 1) = 0 := by
  sorry

/-! ### Lemma 6: complementary parity coverage

Given `j` and `a`, `{(j + a%2) % 3, (j + (a+1)%2) % 3}` =
`{j%3, (j+1)%3}`, since `a%2` and `(a+1)%2` are `{0,1}` in
some order. For any `t ∈ {j%3, (j+1)%3}`, one matches.

Lean proof: `have := Nat.mod_two_eq_zero_or_one a; omega`. -/
private lemma compl_parity_witness (j a : ℕ) (t : ℕ)
    (ht : t < 3)
    (htarg : t = j % 3 ∨ t = (j + 1) % 3) :
    (j + a % 2) % 3 = t ∨
    (j + (a + 1) % 2) % 3 = t := by
  sorry

/-! ### Lemma 7: two pairs with different phases → coverage split

`{j%3, (j+1)%3}` covers 2 of {0,1,2}. Two pairs with distinct
base residues `j₁%3 ≠ j₂%3` cover all 3.

Lean proof: `omega` after `have := Nat.mod_lt j₁ (by omega : 0 < 3)`
and similar. Or `have := Nat.mod_two_eq_zero_or_one ...` style. -/
private lemma two_pairs_cover_split (j₁ j₂ : ℕ)
    (hne : j₁ % 3 ≠ j₂ % 3) (k : ℕ) (hk : k < 3) :
    (k = j₁ % 3 ∨ k = (j₁ + 1) % 3) ∨
    (k = j₂ % 3 ∨ k = (j₂ + 1) % 3) := by
  sorry

/-! ### Lemma 8: idx of last element (m-1) is s-1

m-1 = s*q + r - 1. We show m-1 ≥ bd = r*(q+1).
bd = r*q + r. m-1 = s*q + r - 1. m-1 - bd = (s-r)*q - 1.
Since s > r and q ≥ 1: (s-r)*q ≥ 1, so m-1 ≥ bd. ✓

idx(m-1) = r + (m-1-bd)/q = r + ((s-r)*q - 1)/q.
Write (s-r)*q - 1 = (s-r-1)*q + (q-1).
Since q-1 < q: ((s-r-1)*q + (q-1))/q = s-r-1.
So idx(m-1) = r + (s-r-1) = s - 1. ✓ -/
private lemma eqp_idx_last (q r s : ℕ) (hq : 0 < q)
    (hr : r < s) (hs : 0 < s) :
    eqp_idx q r (s * q + r - 1) = s - 1 := by
  sorry

/-! ### Lemma 9: pair 1 straddle → gap = 2

See Step 5 in the top-level proof for the full case analysis.

Summary: Assume `gap = 1`. From `hstrad` and `hv_hi`:
`v = equiEndpoint(j₀+1) - 1`.

Case A (`j₀+1 < s`): `g > interval length ≥ equiEndpoint(j₀+2) -
equiEndpoint(j₀+1)`, so `v+g ≥ equiEndpoint(j₀+2)`.
- Non-wrapping: `(v+g)%m = v+g ≥ equiEndpoint(j₀+2)`, but
  `hvg_hi` says `< equiEndpoint(j₀+2)`. Contradiction.
- Wrapping: need `equiEndpoint(j₀+1) ≤ v+g-m`, i.e., `g ≥ m+1`.
  But `g < 2q < m`. Contradiction.

Case B (`j₀ = s-1`): `v = m-1`, `(v+g)%m = g-1`. For `gap = 1`:
`jg = 0`, need `g-1 < equiEndpoint(1)`. But `g > ⌈m/s⌉`, so
`g-1 ≥ equiEndpoint(1)`. Contradiction. -/
private lemma straddle1_gap2 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : Finpartition.equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < Finpartition.equiEndpoint m s (j₀ + 1))
    (hvg_lo : Finpartition.equiEndpoint m s jg ≤
      (v + g) % m)
    (hvg_hi : (v + g) % m <
      Finpartition.equiEndpoint m s (jg + 1))
    (hstrad : Finpartition.equiEndpoint m s (j₀ + 1) ≤
      v + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨
      (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 2 := by
  sorry

/-! ### Lemma 10: pair 2 straddle → gap = 1

See Step 6 in the top-level proof for the full case analysis.

Summary: Assume `gap = 2`. From `hstrad` and `hvg_hi`:
`(v+g)%m = equiEndpoint(jg+1) - 1`. And
`v ≤ equiEndpoint(j₀+1) - 1` (from `hv_hi`).

The circular arc from `equiEndpoint(j₀+1)` to
`equiEndpoint(jg+1)` spans 2 intervals (each of length ≥ `q`),
so arc length ≥ `2q`.

- Non-wrapping: `g ≥ equiEndpoint(jg+1) - equiEndpoint(j₀+1)
  ≥ 2q`.
- Wrapping: `g ≥ m + equiEndpoint(jg+1) - equiEndpoint(j₀+1)
  ≥ 2q` (the wrapping circular arc still spans 2 intervals).

Either way `g ≥ 2q`, contradicting `g < 2q`. -/
private lemma straddle2_gap1 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : Finpartition.equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < Finpartition.equiEndpoint m s (j₀ + 1))
    (hvg_lo : Finpartition.equiEndpoint m s jg ≤
      (v + g) % m)
    (hvg_hi : (v + g) % m <
      Finpartition.equiEndpoint m s (jg + 1))
    (hstrad : Finpartition.equiEndpoint m s (jg + 1) ≤
      (v + g) % m + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨
      (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 1 := by
  sorry

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
-/
open Finpartition in
private lemma coverage_assembly (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs3_le : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (hg1_lt_m : g + 1 < m)
    (v : ℕ) (hv : v < m) (k : Fin 3) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let idx := fun p => eqp_idx q r p
    let off := fun p => eqp_off q r p
    let c := fun p => (idx (p % m) + off (p % m) % 2) % 3
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    j₀ % 3 ≠ jg % 3 →
    ((jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) →
    j₀ < s →
    jg < s →
    (∀ p, p < m → idx p < s) →
    (∀ p, p < m →
      equiEndpoint m s (idx p) ≤ p ∧
      p < equiEndpoint m s (idx p + 1)) →
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      c (v + a) = k.val := by
  sorry
