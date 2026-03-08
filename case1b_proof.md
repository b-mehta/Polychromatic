# Case 1b: Interval Coloring — Detailed Informal Proof

## Setup

We work in Z_m = {0, 1, ..., m-1} with the set S = {0, 1, g, g+1}.

**Hypotheses:**
- s > 0 is a multiple of 3
- ceil(m/s) < g (i.e., (m + s - 1) / s < g)
- g < 2 * floor(m/s)

**Goal:** Construct a 3-polychromatic coloring of Z_m for the set S.

## Definitions

Let q = floor(m/s) and r = m mod s. We partition {0, ..., m-1} into s consecutive
intervals: the first r intervals have length q+1, the remaining s-r have length q.
We have m = r*(q+1) + (s-r)*q = s*q + r.

**Interval start positions:**
- Interval j starts at position `start(j) = j*q + min(j, r)`.

**Interval index function:**
- `idx(p)` = the unique j in {0, ..., s-1} such that start(j) <= p < start(j+1).
- Concretely: if p < r*(q+1), then idx(p) = p/(q+1); else idx(p) = r + (p - r*(q+1))/q.

**Coloring function:**
- `color(p) = (idx(p) + offset(p) mod 2) mod 3`
  where `offset(p) = p - start(idx(p))` is the position within the interval.

This produces the pattern described in the paper:
- Interval 0: alternating colors 0, 1, 0, 1, ...
- Interval 1: alternating colors 1, 2, 1, 2, ...
- Interval 2: alternating colors 2, 0, 2, 0, ...
- Interval 3: alternating colors 0, 1, 0, 1, ... (repeats since s is a multiple of 3)

## Lemma Sequence

### Lemma 1: Basic interval arithmetic

**Statement:** Under the hypotheses, m >= s, q >= 1, and g >= 2. Moreover,
ceil(m/s) = q + (if r > 0 then 1 else 0), so ceil(m/s) <= q + 1.

**Proof:** From g < 2q we get q >= 1. From g > ceil(m/s) >= 1 we get g >= 2.
Since m = sq + r and s > 0, m >= s*1 = s. The ceiling formula is standard. ∎

### Lemma 2: Coloring is well-defined and 3-valued

**Statement:** For all p in {0, ..., m-1}, color(p) is in {0, 1, 2}.

**Proof:** color(p) is defined as (...) mod 3, which is always in {0, 1, 2}. ∎

### Lemma 3: Coloring is periodic mod m

**Statement:** For all p in N, color(p mod m) = color(p) when we extend
the interval structure cyclically.

**Proof:** Since the intervals partition {0, ..., m-1}, positions are taken mod m.
The coloring depends only on the position mod m. More precisely, for the
formalization we define color on {0, ..., m-1} and evaluate at p mod m. ∎

### Lemma 4: Same-interval pair gets both colors

**Statement:** If p and p+1 are both in interval j (i.e., idx(p) = idx(p+1) = j),
then {color(p), color(p+1)} = {j mod 3, (j+1) mod 3}.

**Proof:** Let d = offset(p). Then offset(p+1) = d+1 (since both are in the
same interval). We have:
- color(p) = (j + d mod 2) mod 3
- color(p+1) = (j + (d+1) mod 2) mod 3 = (j + (1 - d mod 2)) mod 3

Since d mod 2 and 1 - d mod 2 are 0 and 1 in some order, the two colors are
j mod 3 and (j+1) mod 3. ∎

### Lemma 5: Boundary pair analysis

**Statement:** If p is the last element of interval j (idx(p) = j) and p+1 is
the first element of interval j+1 (idx(p+1) = (j+1) mod s), then:
- color(p+1) = ((j+1) mod s) mod 3 = (j+1) mod 3 (since s is a multiple of 3)
- color(p) = (j + (len_j - 1) mod 2) mod 3, where len_j is the length of interval j.

In particular, the pair {p, p+1} always includes color (j+1) mod 3. If len_j is
odd, the pair gets both {j mod 3, (j+1) mod 3}; if len_j is even, both elements
have color (j+1) mod 3.

**Proof:** At position p+1 = start(j+1), the offset is 0, so color = ((j+1) + 0) mod 3.
At position p = start(j) + len_j - 1, the offset is len_j - 1, so
color = (j + (len_j - 1) mod 2) mod 3.
- If len_j is odd: (len_j - 1) mod 2 = 0, color(p) = j mod 3.
- If len_j is even: (len_j - 1) mod 2 = 1, color(p) = (j+1) mod 3. ∎

### Lemma 6: Separation — pairs are in different intervals

**Statement:** For any position v in {0, ..., m-1}, the interval indices of
v and (v + g) mod m differ. More precisely, if v and v+1 are in intervals j0
(and possibly j0+1), then (v+g) mod m and (v+g+1) mod m are NOT in interval j0.

**Proof:** Each interval has length at most ceil(m/s) = q + (1 if r > 0 else 0).
Since g > ceil(m/s), the distance g exceeds the length of any single interval.
Thus, v and v + g cannot be in the same interval (they are more than one full
interval length apart). ∎

### Lemma 7: Gap bound — second pair within 2 intervals of first

**Statement:** If v is in interval j0, then (v+g) mod m is in interval j0+1
or j0+2 (indices mod s), provided v + g < m (non-wrapping case). The same
holds cyclically when wrapping.

**Proof:** Since g < 2q, the position v + g is at most 2q - 1 positions ahead
of v. Since v is in interval j0 (starting at start(j0)), v + g < start(j0) +
ceil(m/s) + 2q - 1. We need to show this is before start(j0 + 3).

start(j0+3) - start(j0) = sum of 3 interval lengths >= 3q.
And ceil(m/s) + 2q - 1 <= (q+1) + 2q - 1 = 3q.

So v + g < start(j0) + 3q <= start(j0 + 3), meaning (v+g) mod m is in
I_{j0}, I_{j0+1}, or I_{j0+2}. By Lemma 6, it's not in I_{j0}.
So it's in I_{j0+1} or I_{j0+2}. ∎

### Lemma 8: No simultaneous straddling

**Statement:** The pairs {v, v+1} and {(v+g) mod m, (v+g+1) mod m} cannot
both straddle interval boundaries.

**Proof:** Suppose pair 1 ({v, v+1}) straddles I_j and I_{j+1}, meaning v is
the last element of I_j and v+1 is the first element of I_{j+1}.

Then (v+1) + (g-1) = v + g. Since g > ceil(m/s) >= len(I_{j+1}), we have
g - 1 >= len(I_{j+1}), so v + g >= (v+1) + len(I_{j+1}) = start(I_{j+2}).

Also, v + g + 1 <= v + 2q = (v+1) + 2q - 1. And
start(I_{j+3}) = start(I_{j+1}) + len(I_{j+1}) + len(I_{j+2}) >= (v+1) + 2q.
So v + g + 1 <= start(I_{j+3}) - 1 + 1 = start(I_{j+3}).

More precisely, v + g + 1 <= (v+1) + 2q - 1 < (v+1) + len(I_{j+1}) + len(I_{j+2})
= start(I_{j+3}), since len(I_{j+1}) + len(I_{j+2}) >= 2q.

So both v+g and v+g+1 are in interval I_{j+2}. Pair 2 does NOT straddle.

By a symmetric argument (subtracting g), if pair 2 straddles, pair 1 doesn't. ∎

### Lemma 9: Color coverage in each case

**Statement:** For any v in {0, ..., m-1}, the set
  {color(v), color(v+1 mod m), color(v+g mod m), color(v+g+1 mod m)}
contains all of {0, 1, 2}.

**Proof:** We split into three cases.

**Case A: Neither pair straddles.**
Pair 1 = {v, v+1} is within interval I_{j0}, contributing both colors
{j0 mod 3, (j0+1) mod 3} (by Lemma 4).
Pair 2 = {v+g, v+g+1} is within interval I_{j_g}, contributing both colors
{j_g mod 3, (j_g+1) mod 3} (by Lemma 4).
By Lemma 7, j_g in {j0+1, j0+2} (mod s).
- If j_g = j0+1: colors = {j0, j0+1} ∪ {j0+1, j0+2} = {j0, j0+1, j0+2} mod 3 = {0,1,2}. ✓
- If j_g = j0+2: colors = {j0, j0+1} ∪ {j0+2, j0+3} = {j0, j0+1, j0+2, j0} mod 3.
  Since j0+3 ≡ j0 (mod 3), this is {j0, j0+1, j0+2} mod 3 = {0,1,2}. ✓

**Case B: Pair 1 straddles I_j / I_{j+1}, pair 2 doesn't.**
By Lemma 8, pair 2 is within I_{j+2}.
Pair 2 contributes {(j+2) mod 3, (j+3) mod 3} = {(j+2) mod 3, j mod 3}.
Pair 1 contributes at least (j+1) mod 3 (by Lemma 5).
Union = {j, j+1, j+2} mod 3 = {0,1,2}. ✓

**Case C: Pair 2 straddles, pair 1 doesn't.**
By the symmetric argument in Lemma 8, pair 1 is within I_{k-1} (where pair 2
straddles I_k / I_{k+1}).
Pair 1 contributes {(k-1) mod 3, k mod 3}.
Pair 2 contributes at least (k+1) mod 3 (by Lemma 5 applied to pair 2).
Union = {k-1, k, k+1} mod 3 = {0,1,2}. ✓ ∎

### Lemma 10: Assembly

**Statement:** `HasPolychromColouring (Fin 3) ({0, 1, g, g+1} : Finset (ZMod m))`

**Proof:** Define chi : ZMod m -> Fin 3 by chi(x) = ⟨color(x.val), ...⟩.
For any n : ZMod m and k : Fin 3, by Lemma 9 applied to v = n.val, there
exists a in {0, 1, g, g+1} such that color((n.val + a) mod m) = k.val.
Using the `lift_coloring_witness` infrastructure (already in Combi.lean),
this lifts to the ZMod m statement. ∎

## Summary of Dependencies

```
Lemma 1 (arithmetic) ─────────────────────────────────┐
Lemma 2 (well-defined) ───────────────────────────────┤
Lemma 3 (periodicity) ────────────────────────────────┤
Lemma 4 (same-interval pair) ─── Lemma 9 (case A) ───┤
Lemma 5 (boundary pair) ──────── Lemma 9 (case B,C) ──┤── Lemma 10 (assembly)
Lemma 6 (separation) ─────────── Lemma 7 (gap bound) ─┤
                                  Lemma 8 (no double) ─┘
```
