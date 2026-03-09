import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Scratch file 4: coverage proof helpers for case_one_interval

## Detailed Informal Proof

We need: ∃ a ∈ {0, 1, g, g+1}, c(v+a) = k.val, where k : Fin 3.

**Definitions**:
- q = m/s, r = m%s, bd = r*(q+1), m = s*q + r
- idx(p) = if p < bd then p/(q+1) else r + (p-bd)/q
- off(p) = if p < bd then p%(q+1) else (p-bd)%q
- c(p) = (idx(p%m) + off(p%m)%2) % 3

**Known**: j₀ = idx(v), jg = idx((v+g)%m), j₀%3 ≠ jg%3, gap ∈ {1,2}.

**Step 1** (Lemma 7): Since j₁%3 ≠ j₂%3 and k < 3, the set
{j₁%3, (j₁+1)%3, j₂%3, (j₂+1)%3} covers {0,1,2}. Proof: exhaust
j₁%3 ∈ {0,1,2}, j₂%3 ∈ {0,1,2}\{j₁%3}, k ∈ {0,1,2}, check each.
So k is in {j₁%3,(j₁+1)%3} or {j₂%3,(j₂+1)%3}.

**Step 2** (Lemmas 3,4,5): For consecutive positions p, p+1:
- idx(p+1) = idx(p) or idx(p)+1, because in both branches of
  the if-then-else, the quotient a/b and (a+1)/b differ by 0 or 1
  (a general fact about ℕ division). The cross-branch case
  (p<bd, p+1≥bd) means p=bd-1, idx(p)=(bd-1)/(q+1)=r-1,
  idx(p+1)=r+0=r=idx(p)+1.
- If idx(p+1)=idx(p) (non-straddling): off(p+1)=off(p)+1. Proof:
  same branch, same quotient. From a/b=(a+1)/b we get
  b*(a/b)+a%b=a and b*(a/b)+(a+1)%b=a+1, so (a+1)%b=a%b+1.
- If idx(p+1)≠idx(p) (straddling): off(p+1)=0. Proof: new quotient.
  From (a+1)/b=a/b+1 we get b*(a/b+1)+(a+1)%b=a+1 and
  b*(a/b)+a%b=a, so b+a%b=a%b+1+(a+1)%b, so (a+1)%b=b-1-a%b+a%b+1
  ...actually simpler: (a+1)%b < b and b*(a/b+1) ≤ a+1, with
  b*(a/b+1)+(a+1)%b = a+1 and b*(a/b)+b ≤ a+1 giving (a+1)%b=a+1-b*(a/b+1).
  From a/b=a%b=... just use omega after rewriting.

**Step 3** (Lemma 6): For a non-straddling pair in interval j:
c(p)=(j+off(p)%2)%3, c(p+1)=(j+(off(p)+1)%2)%3.
Since off(p)%2 ∈ {0,1}, (off(p)+1)%2 = 1-off(p)%2.
So {c(p),c(p+1)} = {(j+0)%3, (j+1)%3} = {j%3, (j+1)%3}.
For any target t ∈ {j%3,(j+1)%3}: if off(p)%2=0 then
c(p)=j%3 and c(p+1)=(j+1)%3; if off(p)%2=1 then
c(p)=(j+1)%3 and c(p+1)=j%3. Either way t is achieved.

**Step 4** (Lemma 8): idx(m-1) = s-1.
m-1 = s*q+r-1. Since s*q ≥ s ≥ 3 > 0, m-1 ≥ r*(q+1)-1 ≥ 0.
Is m-1 < bd? bd = r*(q+1). m-1 = s*q+r-1. For m-1 < bd:
s*q+r-1 < r*(q+1) = r*q+r, so (s-r)*q < 1. Since q≥1 and
s>r, (s-r)*q ≥ 1. Contradiction. So m-1 ≥ bd.
idx(m-1) = r + (m-1-bd)/q = r + (s*q+r-1-r*q-r)/q
         = r + ((s-r)*q-1)/q.
(s-r)*q-1 = (s-r-1)*q + (q-1). So ((s-r)*q-1)/q = s-r-1.
idx(m-1) = r + s-r-1 = s-1. ✓

**Step 5** (Lemma 9): Pair 1 straddle → gap = 2.
Hypothesis: equiEndpoint(j₀+1) ≤ v+1 (v is last in interval j₀).
Combined with v < equiEndpoint(j₀+1), we get v+1 = equiEndpoint(j₀+1).

Key fact: g > ceil(m/s) ≥ equiEndpoint(j₀+2) - equiEndpoint(j₀+1).
Proof: equiEndpoint(j+1) - equiEndpoint(j) = q + (if j < r then 1 else 0)
     ≤ q + 1 ≤ ceil(m/s) = (m+s-1)/s. And g > (m+s-1)/s.

So v+g = equiEndpoint(j₀+1)-1+g ≥ equiEndpoint(j₀+1)+ceil(m/s)-1
       ≥ equiEndpoint(j₀+2)-1+1-1 = equiEndpoint(j₀+2)-1.
Actually more precisely: g > ilen(j₀+1), so g ≥ ilen(j₀+1)+1,
v+g ≥ equiEndpoint(j₀+1)+ilen(j₀+1) = equiEndpoint(j₀+2).

Now assume for contradiction gap = 1, i.e., jg = (j₀+1)%s.
Then (v+g)%m is in interval (j₀+1)%s.

Case A: v+g < m (non-wrapping).
  (v+g)%m = v+g ≥ equiEndpoint(j₀+2).
  But interval (j₀+1)%s = j₀+1 (since j₀+1 ≤ s-1 or j₀+1=s→
  (j₀+1)%s=0) ends at equiEndpoint(j₀+2) (if j₀+1<s) or
  equiEndpoint(1) (if j₀+1=s).
  If j₀+1 < s: v+g ≥ equiEndpoint(j₀+2) means v+g is NOT in
  interval j₀+1 (which is [equiEndpoint(j₀+1), equiEndpoint(j₀+2))).
  Contradiction.
  If j₀+1 = s (j₀=s-1): equiEndpoint(s) = m but v+g < m,
  so v+g < equiEndpoint(s) = m. And v+g ≥ equiEndpoint(s) = m.
  Contradiction.

Case B: v+g ≥ m (wrapping). (v+g)%m = v+g-m.
  Sub-case j₀ < s-1: (j₀+1)%s = j₀+1. For gap=1, (v+g)%m
  must be in interval j₀+1: equiEndpoint(j₀+1) ≤ v+g-m.
  But v < equiEndpoint(j₀+1) and g < 2q, so
  v+g-m < equiEndpoint(j₀+1)+2q-m ≤ (m-q)+2q-m = q.
  And equiEndpoint(j₀+1) ≥ equiEndpoint(1) ≥ q.
  So v+g-m < q ≤ equiEndpoint(j₀+1). Contradiction.

  Sub-case j₀ = s-1: (j₀+1)%s = 0. For gap=1, jg=0.
  v = m-1 (last element, since equiEndpoint(s)=m and
  equiEndpoint(s) ≤ v+1 ≤ m, and v < m). (v+g)%m = g-1.
  idx(g-1) must be 0. But g > ceil(m/s). If r>0: ceil=q+1,
  g ≥ q+2, g-1 ≥ q+1 ≥ equiEndpoint(1). If r=0: ceil=q,
  g ≥ q+1, g-1 ≥ q = equiEndpoint(1).
  In both cases g-1 ≥ equiEndpoint(1), so g-1 is NOT in
  interval 0 (which is [0, equiEndpoint(1))). So idx(g-1) ≠ 0.
  Contradiction.

**Step 6** (Lemma 10): Pair 2 straddle → gap = 1.
Hypothesis: equiEndpoint(jg+1) ≤ (v+g)%m + 1 (v+g is last in jg).
Combined with (v+g)%m < equiEndpoint(jg+1), we get
(v+g)%m + 1 = equiEndpoint(jg+1).

Assume for contradiction gap = 2.
Then jg = (j₀+2)%s. The distance from v (in interval j₀) to
(v+g)%m (last element of interval jg) spans at least 2 full
intervals: ilen(j₀+1) + ilen(j₀+2) (possibly wrapping).
Each interval has length ≥ q, so g ≥ 2q.
But h_ub says g < 2q. Contradiction.

More precisely: v ≥ equiEndpoint(j₀), and
(v+g)%m = equiEndpoint(jg+1)-1.
g = (v+g) - v ≥ equiEndpoint(jg+1)-1 - (equiEndpoint(j₀+1)-1)
  = equiEndpoint(jg+1) - equiEndpoint(j₀+1).
If jg = j₀+2 (non-wrapping): this is
equiEndpoint(j₀+3) - equiEndpoint(j₀+1) = ilen(j₀+1)+ilen(j₀+2) ≥ 2q.
So g ≥ 2q. But g < 2q. Contradiction.
Wrapping cases are similar (the sum of interval lengths ≥ 2q).

**Step 7** (Main assembly in case_one_interval):
- By Lemma 7, k.val ∈ {j₀%3,(j₀+1)%3} or {jg%3,(jg+1)%3}.
- Case split on straddling of each pair.
- Neither straddles: Lemma 6 gives witnesses from each pair.
- Pair 1 straddles: gap=2 (Lemma 9), pair 2 non-straddles.
  c(v+1) has off=0 so c(v+1)=(j₀+1)%3 (from idx step + 3|s).
  Pair 2 covers {(j₀+2)%3, j₀%3}. All 3 colors present.
- Pair 2 straddles: gap=1 (Lemma 10), pair 1 non-straddles.
  Pair 1 covers {j₀%3, (j₀+1)%3}. c(v+g+1) has off=0 so
  c(v+g+1)=(jg+1)%3=(j₀+2)%3. All 3 colors present.
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
  set bd := r * (q + 1)
  unfold eqp_idx
  split_ifs with h1 h2 h3 h4
  · -- p+1 < bd, p < bd: both in first branch
    exact div_step p (q + 1) (by omega)
  · -- p+1 ≥ bd, p < bd: cross branch, p+1 = bd
    have hpeq : p + 1 = bd := by omega
    right
    have hr_pos : 1 ≤ r := by
      by_contra h; push_neg at h
      have : r = 0 := by omega; omega
    have hidx_p : p / (q + 1) = r - 1 := by
      have h_dm := Nat.div_add_mod p (q + 1)
      have h_ml := Nat.mod_lt p (show 0 < q + 1 by omega)
      have hle : p / (q + 1) ≤ r - 1 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
        omega
      have hge : r - 1 ≤ p / (q + 1) := by
        rw [Nat.le_div_iff_mul_le (by omega)]
        omega
      omega
    rw [hidx_p, hpeq, Nat.sub_self, Nat.zero_div]; omega
  · -- p+1 < bd, p ≥ bd: impossible
    omega
  · -- p+1 ≥ bd, p ≥ bd: both in second branch
    have hsub : p + 1 - bd = (p - bd) + 1 := by omega
    rw [hsub]
    have key := div_step (p - bd) q hq; omega

/-! ### Lemma 4: same idx → off increases by 1

Proof: If eqp_idx(p+1) = eqp_idx(p), then p and p+1 are in
the same branch and have the same quotient.

Case 1: Both in first branch (p < bd, p+1 < bd).
  idx(p) = p/(q+1) = (p+1)/(q+1). By the general fact:
  if a/b = (a+1)/b then (a+1)%b = a%b + 1.
  Proof of general fact: from Nat.div_add_mod,
  b*(a/b) + a%b = a and b*((a+1)/b) + (a+1)%b = a+1.
  Since a/b = (a+1)/b, subtract: (a+1)%b - a%b = 1.

Case 2: Both in second branch (p ≥ bd, p+1 ≥ bd).
  Same argument with (p-bd)/q = (p+1-bd)/q.
  (p+1-bd)%q = (p-bd)%q + 1.

Case 3: Cross-branch impossible (would change idx). -/
private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by
  sorry

/-! ### Lemma 5: different idx → off is 0

Proof: If eqp_idx(p+1) ≠ eqp_idx(p), then either:

Case 1: Both in first branch, quotient changes.
  p/(q+1) ≠ (p+1)/(q+1), i.e., (p+1)/(q+1) = p/(q+1)+1.
  General fact: if (a+1)/b = a/b + 1, then (a+1)%b = 0.
  Proof: b*(a/b+1) + (a+1)%b = a+1 and b*(a/b) + a%b = a.
  So b + (a+1)%b = a%b + 1 ≤ b. Hence (a+1)%b = 0.
  ...actually from omega: b*(a/b+1) ≤ a+1 and (a+1)%b < b
  gives (a+1)%b = a+1 - b*(a/b+1). And a+1 = b*(a/b)+a%b+1,
  so (a+1)%b = b*(a/b)+a%b+1 - b*(a/b+1) = a%b+1-b.
  Since a%b < b, a%b+1 ≤ b, so (a+1)%b = a%b+1-b. For this
  to be ≥ 0: a%b = b-1. Then (a+1)%b = 0. ✓

Case 2: Both in second branch, quotient changes. Same.

Case 3: Cross-branch (p < bd, p+1 ≥ bd).
  p+1 = bd. off(p+1) = (bd - bd) % q = 0 % q = 0. ✓ -/
private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) ≠ eqp_idx q r p) :
    eqp_off q r (p + 1) = 0 := by
  sorry

/-! ### Lemma 6: complementary parity coverage

Given j and a, the pair (j+a%2)%3 and (j+(a+1)%2)%3 covers
{j%3, (j+1)%3}. So for any target t ∈ {j%3, (j+1)%3}, one
of the two expressions equals t.

Proof: a%2 = 0 or a%2 = 1.
If a%2 = 0: (a+1)%2 = 1. Values: (j+0)%3 = j%3, (j+1)%3.
If a%2 = 1: (a+1)%2 = 0. Values: (j+1)%3, (j+0)%3 = j%3.
Either way, both j%3 and (j+1)%3 appear.
For any t ∈ {j%3, (j+1)%3}, one of the pair equals t. -/
private lemma compl_parity_witness (j a : ℕ) (t : ℕ)
    (ht : t < 3)
    (htarg : t = j % 3 ∨ t = (j + 1) % 3) :
    (j + a % 2) % 3 = t ∨
    (j + (a + 1) % 2) % 3 = t := by
  sorry

/-! ### Lemma 7: two pairs with different phases → coverage split

For j₁%3 ≠ j₂%3 and k < 3: k is in {j₁%3, (j₁+1)%3} or
{j₂%3, (j₂+1)%3}. The pair {j%3, (j+1)%3} covers 2 of the
3 residues mod 3. Two such pairs with different base residues
cover all 3.

Proof: Exhaust j₁%3 ∈ {0,1,2}, j₂%3 ∈ {0,1,2}\{j₁%3},
k ∈ {0,1,2}. Each of the 18 cases is verified directly. -/
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

Hypothesis: v is last element of interval j₀ (equiEndpoint(j₀+1)
≤ v+1, combined with v < equiEndpoint(j₀+1) gives equality).

Key arithmetic: equiEndpoint(j₀+2) - equiEndpoint(j₀+1)
= ilen(j₀+1) ≤ q+1 ≤ ceil(m/s) < g.
So v+g = (v+1)-1+g = equiEndpoint(j₀+1)-1+g ≥ equiEndpoint(j₀+2).

Assume gap = 1, derive contradiction:
(v+g)%m must be in interval (j₀+1)%s.

Non-wrapping (v+g < m): (v+g)%m = v+g ≥ equiEndpoint(j₀+2).
  Interval (j₀+1) is [equiEndpoint(j₀+1), equiEndpoint(j₀+2)).
  So v+g ≥ equiEndpoint(j₀+2) means NOT in this interval.
  Contradiction with gap=1.

Wrapping (v+g ≥ m), j₀ < s-1: (v+g)%m = v+g-m.
  v < equiEndpoint(j₀+1) ≤ equiEndpoint(s-1) = m - q.
  So v+g-m < (m-q)+g-m = g-q < 2q-q = q.
  equiEndpoint(j₀+1) ≥ equiEndpoint(1) ≥ q.
  So v+g-m < q ≤ equiEndpoint(j₀+1).
  For gap=1, need equiEndpoint(j₀+1) ≤ (v+g)%m. Contradiction.

Wrapping, j₀ = s-1: v = m-1, (v+g)%m = g-1.
  For gap=1: jg = 0, need idx(g-1) = 0, need g-1 < equiEndpoint(1).
  equiEndpoint(1) = q + min(r,1) ≤ q+1.
  g > ceil(m/s) ≥ q (with equality iff r=0).
  If r=0: g > q, g-1 ≥ q = equiEndpoint(1). Contradiction.
  If r>0: g > q+1, g-1 ≥ q+1 = equiEndpoint(1). Contradiction. -/
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

Hypothesis: (v+g)%m is last element of interval jg
(equiEndpoint(jg+1) ≤ (v+g)%m + 1, combined with
(v+g)%m < equiEndpoint(jg+1) gives equality).
So (v+g)%m + 1 = equiEndpoint(jg+1).

Assume gap = 2, derive contradiction:
jg = (j₀+2)%s. We need g ≥ 2q.

In the non-wrapping case (v+g < m):
(v+g)%m = v+g = equiEndpoint(jg+1)-1.
v ≥ equiEndpoint(j₀) and jg = j₀+2 (non-wrapping).
g = v+g - v = equiEndpoint(j₀+3)-1 - v.
v < equiEndpoint(j₀+1), so g > equiEndpoint(j₀+3)-1
- equiEndpoint(j₀+1) + 1 - 1 = equiEndpoint(j₀+3) -
equiEndpoint(j₀+1) - 1.
equiEndpoint(j₀+3) - equiEndpoint(j₀+1) =
ilen(j₀+1) + ilen(j₀+2) ≥ 2q.
So g ≥ 2q. But g < 2q. Contradiction.

Wrapping case is similar: the total span of 2 intervals is
≥ 2q, forcing g ≥ 2q, which contradicts h_ub. -/
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
