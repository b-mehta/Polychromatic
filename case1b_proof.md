# Case 1b: Interval Coloring — Detailed Proof for Formalization

## Setup

We work in `ℕ` with positions in `[0, m)`. The set is `S = {0, 1, g, g+1}`.

**Parameters:**
- `s > 0` with `3 ∣ s`
- `q = m / s`, `r = m % s`, so `m = s*q + r` with `0 ≤ r < s`
- `⌈m/s⌉ = (m + s - 1) / s < g` (lower bound)
- `g < 2q` (upper bound)
- These imply: `q ≥ 1`, `s ≥ 3`, `g + 1 < m`

**Interval partition:**
- `bd = r * (q + 1)` (boundary between long and short intervals)
- First `r` intervals have length `q + 1`, remaining `s - r` have length `q`
- `bd ≤ m` since `r*(q+1) + (s-r)*q = sq + r = m`

**Interval index and offset for position `p < m`:**
- If `p < bd`: `idx(p) = p / (q+1)`, `off(p) = p % (q+1)`
- If `p ≥ bd`: `idx(p) = r + (p - bd) / q`, `off(p) = (p - bd) % q`

**Coloring:**
- `c(p) = (idx(p % m) + off(p % m) % 2) % 3`

**Goal:** For all `v < m` and `k < 3`, there exists `a ∈ {0, 1, g, g+1}` with `c(v + a) = k`.

Since `c` is periodic mod `m` (by definition), `c(v + a) = c((v + a) % m)`.

## Detailed Proof

### Step 1: Top-level case split on `v < bd`

We split on whether `v < bd` (v is in the long-interval region) or `v ≥ bd` (short-interval region). In each branch, `idx(v)` and `off(v)` simplify to concrete division/mod expressions.

### Step 2: Within each branch, determine straddling of pair 1

Pair 1 is `{v, v+1}`. It straddles iff `v` is the last element of its interval:
- Long interval case (`v < bd`): straddles iff `off(v) = q`, i.e., `v % (q+1) = q`
- Short interval case (`v ≥ bd`): straddles iff `off(v) = q - 1`, i.e., `(v - bd) % q = q - 1`

When NOT straddling: `v+1` is in the same interval, `off(v+1) = off(v) + 1`, and the two colors `c(v)`, `c(v+1)` are `{j₀ % 3, (j₀+1) % 3}` (both consecutive phases).

When straddling: `v+1` starts the next interval with `off = 0`, so `c(v+1) = (j₀+1) % 3`.

### Step 3: Compute `idx` for the second pair

The second pair is `{(v+g) % m, (v+g+1) % m}`.

**Sub-case split on wrapping:** Since `v < m` and `g < 2q ≤ 2m/3 < m` (because `s ≥ 3`), we have `v + g < 2m`. So `(v+g) % m = v+g` if `v+g < m`, or `v+g-m` if `v+g ≥ m`.

### Step 4: Gap bound (the key arithmetic)

We need: `idx((v+g) % m)` differs from `idx(v)` by 1 or 2 (cyclically mod s).

**Proof sketch:** The start position of interval `j` is `start(j) = j*q + min(j, r)`.
- `start(j+1) - start(j) = q + (1 if j < r else 0)` = length of interval `j`.
- Max interval length = `q + 1` (when `r > 0`), min = `q`.

Since `g > ⌈m/s⌉ ≥ q + (1 if r > 0 else 0) ≥ len(j₀)`:
  - `v + g ≥ start(j₀) + g > start(j₀) + len(j₀) - 1 = start(j₀+1) - 1`
  - So `v + g ≥ start(j₀ + 1)`, meaning `(v+g) % m` is NOT in interval `j₀`.

Since `g < 2q ≤ len(j₀+1) + len(j₀+2)` (sum of any 2 interval lengths ≥ 2q):
  - `v + g < start(j₀+1) + len(j₀+1) + len(j₀+2) - 1 = start(j₀+3) - 1`... wait.

More precisely: `v < start(j₀+1)`, so `v + g < start(j₀+1) + g ≤ start(j₀+1) + 2q - 1`. And `start(j₀+3) - start(j₀+1) = len(j₀+1) + len(j₀+2) ≥ 2q`. So `v + g < start(j₀+1) + 2q ≤ start(j₀+3) + 1`... hmm, need to be more careful.

Actually: `v + g ≤ (start(j₀+1) - 1) + (2q - 1) = start(j₀+1) + 2q - 2`. And `start(j₀+3) = start(j₀+1) + len(j₀+1) + len(j₀+2) ≥ start(j₀+1) + 2q`. So `v + g ≤ start(j₀+1) + 2q - 2 < start(j₀+3)`. ✓

Combined: `start(j₀+1) ≤ (v+g) % m < start(j₀+3)` (cyclically). So `idx((v+g) % m) ∈ {(j₀+1) % s, (j₀+2) % s}`.

### Step 5: Phase difference from `3 | s`

Since `idx((v+g) % m) ∈ {(j₀+1) % s, (j₀+2) % s}` and `3 | s`:
- `((j₀+1) % s) % 3 = (j₀+1) % 3 ≠ j₀ % 3` (by `Nat.mod_mod_of_dvd`)
- `((j₀+2) % s) % 3 = (j₀+2) % 3 ≠ j₀ % 3`

So `idx(v) % 3 ≠ idx((v+g) % m) % 3`.

### Step 6: No double straddling

Claim: At most one of the two pairs straddles.

**Proof:** Suppose pair 1 straddles at boundary j₀/j₀+1. Then `v = start(j₀+1) - 1` and `v+1 = start(j₀+1)`.

Now `(v+g) % m = (start(j₀+1) - 1 + g) % m`. Since `g > ceil(m/s) ≥ len(j₀+1)`, we have:
- `v + g ≥ start(j₀+1) - 1 + len(j₀+1) = start(j₀+2) - 1`
- `v + g + 1 ≥ start(j₀+2)`

And from step 4, `(v+g+1) % m < start(j₀+3)`. Since `start(j₀+2) ≤ (v+g) % m` and `(v+g+1) % m < start(j₀+3)`, and `start(j₀+2)` to `start(j₀+3)` is exactly interval `j₀+2`, both elements of pair 2 are in interval `(j₀+2) % s`. So pair 2 does NOT straddle.

(Symmetric argument for pair 2 straddling implies pair 1 doesn't.)

### Step 7: Coverage — Case A (neither pair straddles)

Pair 1 in interval `j₀` gives colors `{j₀ % 3, (j₀+1) % 3}` (by Step 2).
Pair 2 in interval `jg` gives colors `{jg % 3, (jg+1) % 3}`.
Since `j₀ % 3 ≠ jg % 3` (Step 5), the union of two sets of consecutive mod-3 values with different phases covers `{0, 1, 2}`.

**Proof of coverage fact:** If `a % 3 ≠ b % 3`, then `{a%3, (a+1)%3} ∪ {b%3, (b+1)%3} = {0,1,2}`. This is `two_pairs_cover` — proven by case-splitting on `a%3 ∈ {0,1,2}`, `b%3 ∈ {0,1,2}`, `k ∈ {0,1,2}`.

### Step 8: Coverage — Case B (pair 1 straddles)

Pair 1 contributes at least `(j₀+1) % 3` (Step 2, straddling case).
By Step 6, pair 2 doesn't straddle and is in interval `(j₀+2) % s`.
Pair 2 gives `{(j₀+2) % 3, (j₀+3) % 3} = {(j₀+2) % 3, j₀ % 3}`.
Together: `{j₀ % 3, (j₀+1) % 3, (j₀+2) % 3} = {0, 1, 2}`. ✓

### Step 9: Coverage — Case C (pair 2 straddles)

Symmetric to Case B. Pair 2 contributes `(jg+1) % 3`. Pair 1 doesn't straddle and gives `{j₀ % 3, (j₀+1) % 3}`. Since `jg ∈ {j₀+1, j₀+2}` (mod s), `(jg+1) % 3` completes the coverage.

### Step 10: Assembly via `endgame_witness`

In each case, identify 3 witnesses `a₀, a₁, a₂ ∈ {0, 1, g, g+1}` giving colors `s`, `(s+1)%3`, `(s+2)%3` for some `s < 3`. Apply `endgame_witness` to get the existential.

## Proposed Lemma Decomposition for Lean

### Lemma 1: `idx_lt` — idx is in range
For `p < m`: `idx(p) < s`.

### Lemma 2: `off_lt` — off is bounded by interval length
For `p < m`: if `p < bd` then `off(p) < q + 1`, else `off(p) < q`.

### Lemma 3: `idx_succ_same` — consecutive in same interval
If `p < m`, `p + 1 < m`, and `off(p) + 1 < len(idx(p))`, then `idx(p+1) = idx(p)` and `off(p+1) = off(p) + 1`.

### Lemma 4: `idx_succ_boundary` — consecutive straddling
If `p < m` and `off(p) + 1 = len(idx(p))`, then `idx((p+1) % m) = (idx(p) + 1) % s` and `off((p+1) % m) = 0`.

### Lemma 5: `gap_lower` — gap skips at least one interval
For `v < m`: `idx((v+g) % m) ≠ idx(v)` (mod s).

### Lemma 6: `gap_upper` — gap skips at most two intervals
For `v < m`: `idx((v+g) % m) ∈ {(idx(v)+1) % s, (idx(v)+2) % s}`.

### Lemma 7: `phase_ne` — phases differ mod 3
If `j₁ ∈ {(j₀+1)%s, (j₀+2)%s}` and `3 | s`, then `j₁ % 3 ≠ j₀ % 3`.

### Lemma 8: `no_double_straddle` — at most one pair straddles
If pair 1 straddles at `j₀/j₀+1`, then `idx((v+g) % m) = idx((v+g+1) % m) = (j₀+2) % s`.

### Lemma 9: `two_pairs_cover` — coverage from two non-straddling pairs
If `a % 3 ≠ b % 3` and `k < 3`, then `k ∈ {a%3, (a+1)%3, b%3, (b+1)%3}`.

### Lemma 10: Assembly
Combine lemmas 1–9 via `endgame_witness` + `lift_coloring_witness`.

## Key Implementation Notes

1. **The `by_cases h : v < bd` split** should come FIRST in the proof, before reasoning about idx/off. This resolves the conditional in idx/off and makes everything concrete arithmetic.

2. **Within each branch**, idx(v) and off(v) become simple expressions (`v / (q+1)` or `r + (v-bd)/q`) that omega/grind can handle.

3. **Wrapping:** `v + g < 2m` always (since `g < m`), so `(v+g) % m = v+g` or `v+g-m`. Need a sub-case-split on this.

4. **The gap bound (Lemmas 5-6) is the hardest part.** It requires showing:
   - Lower bound: the distance `g` exceeds any single interval length (`q+1`)
   - Upper bound: the distance `g` is less than 2 times the minimum interval length (`2q`)
   - Converting these to interval index bounds via the start position formula

5. **`omega` struggles with `3 ∣ s`** in context. Use `obtain ⟨t, ht⟩ := hs3; subst ht` only at the moment needed (e.g., Lemma 7), not globally. For arithmetic that doesn't need `3|s`, keep `hs3` abstract.

6. **Lemma 7 (`phase_ne`)** needs special care: for the wrapping case where `(j₀+1)%s` wraps around (j₀ = s-1), use `Nat.mul_add_mod` after rewriting `s-1 = 3*(t-1) + 2` etc.
