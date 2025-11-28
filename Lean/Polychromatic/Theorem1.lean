import Polychromatic.FourThree.Theory
import Polychromatic.FourThree.Compute

/-!
# Theorem 1: Formal Sketch

This file contains a formal sketch of the proof of Theorem 1 from the paper
"Polychromatic Colorings of Arbitrary Rectangular Partitions" (arXiv:1704.00042).

## Main Theorem

Every set S ⊆ ℤ of 4 integers has a 3-polychromatic colouring.

## Proof Structure

The proof proceeds by reduction and case analysis:

1. **Reduction**: By `suffices_minimal` and `suffices_triple`, it suffices to prove
   for sets of the form `{0, a, b, c}` with `0 < a < b < c`.
2. **GCD reduction**: By `suffices_gcd`, we may assume `gcd(a, b, c) = 1`.
3. **Flip symmetry**: By `suffices_flip`, we may assume `a + b ≤ c`.
4. **Small cases**: For `c < 289`, use `allC_289` (computer verification).
5. **Large cases**: For `c ≥ 289`, use `m = c - a + b` and work in `ZMod m`.

For large cases, the key transformation uses `polychromNumber_zmod_le`:
if `m = c - a + b`, then `{0, a, b, c}` and `{0, b - a, b, 2b - a}` have
the same polychromatic number in `ZMod m`.

Let `S = {0, b - a, b, 2b - a}` in `ZMod m`. The key observation
is that `S` contains two repeated differences: `b - a` and `b`.

Define:
- `d₁ = gcd(b, m)`
- `d₂ = gcd(b - a, m)`

Since `gcd(a, b, c) = 1`, we have `gcd(d₁, d₂) = 1`.

**Main Case 1 (Single cycle)**: `min(d₁, d₂) = 1`

Assume WLOG that `d₁ = 1`. Then there exists `g` with `2 ≤ g ≤ m - 2` such that
`g · b ≡ b - a (mod m)`, so `S = {0, 1, g, g + 1}`.

- Subcase 1a: g = 2, 3, or 4 (handled by Subcase 1c)
- Subcase 1b: 5 ≤ g < 2⌊m/s⌋ (interval coloring)
- Subcase 1c: m ≡ ±1, ±2, +4, +5 (mod 3g) (multiply by 3, use Table 1)
- Subcase 1d: m = 3g or 3g + 3 (pattern 012012...)

**Main Case 2 (Multiple cycles)**: `min(d₁, d₂) > 1`

Choose `d₁` to be the smallest not divisible by 3. Let `e₁ = m/d₁`.
Partition `ZMod m` into `d₁` cycles `C₀, C₁, ..., C_{d₁-1}` of length `e₁`.

- Subcase 2a: e₁ is even
- Subcase 2b: d₁ is even and e₁ is odd
- Subcase 2c: d₁ and e₁ are both odd, with e₁ ≤ 17
- Subcase 2d: d₁ and e₁ are both odd, with e₁ ≥ 19

## References

* arXiv:1704.00042

-/

open Finset

/-! ### Key Definitions -/

/-- The parameter `m = c - a + b` used in the proof for large cases. -/
def mParam (a b c : ℤ) : ℤ := c - a + b

/-- The transformed set `{0, b - a, b, 2b - a}` in `ZMod m`. -/
def transformedSet (a b c : ℤ) : Finset ℤ := {0, b - a, b, 2 * b - a}

/-- The parameter `d₁ = gcd(b, m)`. -/
def d₁Param (b m : ℕ) : ℕ := Nat.gcd b m

/-- The parameter `d₂ = gcd(b - a, m)`. -/
def d₂Param (a b m : ℕ) : ℕ := Nat.gcd (b - a) m

/-- The parameter `e₁ = m / d₁`. -/
def e₁Param (m d₁ : ℕ) : ℕ := m / d₁

/-- The parameter `e₂ = m / d₂`. -/
def e₂Param (m d₂ : ℕ) : ℕ := m / d₂

/-! ### GCD Property -/

/-- When `gcd(a, b, c) = 1`, we have `gcd(d₁, d₂) = 1`.

Note: This lemma assumes `a < b` so that `b - a` doesn't underflow. -/
lemma gcd_d₁_d₂_eq_one {a b c m : ℕ} (hab : a < b) (hm : m = c - a + b)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) :
    Nat.gcd (d₁Param b m) (d₂Param a b m) = 1 := by
  sorry

/-! ### Main Case 1: Single Cycle -/

/-- Main Case 1: When `min(d₁, d₂) = 1`. -/
def singleCycleCase (a b m : ℕ) : Prop :=
  min (d₁Param b m) (d₂Param a b m) = 1

/-- In the single cycle case with `d₁ = 1`, there exists `2 ≤ g ≤ m - 2` such that
`g * b ≡ b - a (mod m)`.

Note: This lemma assumes `a ≤ b` so that `b - a` doesn't underflow. -/
lemma exists_g_singleCycle {a b m : ℕ} (hab : a ≤ b) (hd₁ : d₁Param b m = 1) (hm : 2 < m) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ m - 2 ∧ g * b % m = (b - a) % m := by
  sorry

/-- Subcase 1a: g = 2, 3, or 4. Reduces to checking specific small sets. -/
lemma subcase_1a {m g : ℕ} (hg : g = 2 ∨ g = 3 ∨ g = 4) (hm : 289 ≤ m) :
    HasPolychromColouring (Fin 3) (({0, 1, g, g + 1} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- Subcase 1b: 5 ≤ g < 2⌊m/s⌋. Use interval coloring. -/
lemma subcase_1b {m g s : ℕ} (hg_lo : 5 ≤ g) (hg_hi : g < 2 * (m / s))
    (hs : s = 3 * (Nat.find (⟨3, by omega⟩ : ∃ t : ℕ, t ≥ 3 ∧ g > (m + t - 1) / t))) :
    HasPolychromColouring (Fin 3) (({0, 1, g, g + 1} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- Subcase 1c: m ≡ 3g - 2, 3g - 1, 3g + 1, 3g + 2, 3g + 4, or 3g + 5.
    Reduces to checking one of 5 specific sets using Lemma 12(iv). -/
lemma subcase_1c {m g : ℕ} (hm : m % 3 ≠ 0)
    (hcase : m = 3 * g - 2 ∨ m = 3 * g - 1 ∨ m = 3 * g + 1 ∨
             m = 3 * g + 2 ∨ m = 3 * g + 4 ∨ m = 3 * g + 5) :
    HasPolychromColouring (Fin 3) (({0, 1, g, g + 1} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- The specific sets handled in Subcase 1c. -/
def subcase1cSets : List (Finset ℤ) :=
  [{0, 2, 3, 5}, {0, 1, 3, 4}, {0, 1, 2, 3}, {0, 3, 4, 7}, {0, 3, 5, 8}]

/-- Each set in Subcase 1c has a periodic 3-colouring using intervals of length r and r+1. -/
lemma subcase_1c_periodic {S : Finset ℤ} (hS : S ∈ subcase1cSets) {m : ℕ} (hm : 72 ≤ m) :
    HasPolychromColouring (Fin 3) (S.image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- Subcase 1d: m = 3g or m = 3g + 3. Use pattern 012012...012. -/
lemma subcase_1d {m g : ℕ} (hcase : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) (({0, 1, g, g + 1} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- Main Case 1: Single cycle case is solvable. -/
lemma singleCycle_solvable {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) (hc : 289 ≤ c)
    (hSingle : singleCycleCase a b (c - a + b)) :
    Accept a b c := by
  sorry

/-! ### Main Case 2: Multiple Cycles

In this section, all lemmas assume `0 < a < b < c`, which ensures that:
- `b - a > 0` (no underflow)
- `c - a + b = c + b - a > 0` (no underflow, since `a < c + b`)
-/

/-- Main Case 2: When `min(d₁, d₂) > 1`. -/
def multipleCycleCase (a b m : ℕ) : Prop :=
  min (d₁Param b m) (d₂Param a b m) > 1

/-- The cycles `Cᵢ` partition `ZMod m` into `d₁` cycles of length `e₁`.
Here `b_sub_a` should be `b - a` (assuming `a < b`). -/
def cycle (b_sub_a b : ℕ) (m : ℕ) (i : ℕ) : Finset (ZMod m) :=
  (Finset.range (m / Nat.gcd b m)).image fun j =>
    (i * b_sub_a + j * b : ZMod m)

/-- The cycles form a partition of `ZMod m`. -/
lemma cycles_partition {a b m : ℕ} (hm : 0 < m) :
    (Finset.range (d₁Param b m)).biUnion (cycle (b - a) b m) = Finset.univ := by
  sorry

/-- Each translate of S intersects two consecutive cycles at two consecutive positions. -/
lemma translate_intersects_cycles {a b m : ℕ} (d₁ := d₁Param b m) (e₁ := e₁Param m d₁)
    (n : ZMod m) :
    ∃ i j : ℕ, i < d₁ ∧ j < e₁ ∧
      (n +ᵥ ({0, b - a, b, 2 * b - a} : Finset ℤ).image (Int.cast : ℤ → ZMod m) : Finset (ZMod m)) =
      {(i * (b - a) + j * b : ZMod m), (i * (b - a) + (j + 1) * b : ZMod m),
       ((i + 1) * (b - a) + j * b : ZMod m), ((i + 1) * (b - a) + (j + 1) * b : ZMod m)} := by
  sorry

/-- Subcase 2a: e₁ is even. Color cycles alternately with 0101...01 and 0202...02.

Note: The hypothesis `a < b` ensures `b - a` and `c - a + b` don't underflow. -/
lemma subcase_2a {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (d₁ := d₁Param b (c - a + b)) (e₁ := e₁Param (c - a + b) d₁)
    (he₁_even : Even e₁) :
    HasPolychromColouring (Fin 3)
      ((transformedSet a b c).image (Int.cast : ℤ → ZMod (c - a + b))) := by
  sorry

/-- Subcase 2b: d₁ is even and e₁ is odd. -/
lemma subcase_2b {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (d₁ := d₁Param b (c - a + b)) (e₁ := e₁Param (c - a + b) d₁)
    (hd₁_even : Even d₁) (he₁_odd : Odd e₁) :
    HasPolychromColouring (Fin 3)
      ((transformedSet a b c).image (Int.cast : ℤ → ZMod (c - a + b))) := by
  sorry

/-- Subcase 2c: d₁ and e₁ are both odd, with e₁ ≤ 17.
    In this case, e₁ must be a multiple of 3, and we use patterns 012012..., 120120..., 201201... -/
lemma subcase_2c {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (d₁ := d₁Param b (c - a + b)) (e₁ := e₁Param (c - a + b) d₁)
    (hd₁_odd : Odd d₁) (he₁_odd : Odd e₁) (he₁_small : e₁ ≤ 17) :
    HasPolychromColouring (Fin 3)
      ((transformedSet a b c).image (Int.cast : ℤ → ZMod (c - a + b))) := by
  sorry

/-- In Subcase 2c, e₁ must be divisible by 3. -/
lemma subcase_2c_e₁_div_3 {a b c : ℕ} (hab : a < b) (hbc : b < c) (hc : 289 ≤ c)
    (d₁ := d₁Param b (c - a + b)) (d₂ := d₂Param a b (c - a + b))
    (e₁ := e₁Param (c - a + b) d₁) (e₂ := e₂Param (c - a + b) d₂)
    (hd₁_odd : Odd d₁) (he₁_odd : Odd e₁) (he₁_small : e₁ ≤ 17)
    (hMultiple : multipleCycleCase a b (c - a + b))
    (hd₁_not_div_3 : ¬ 3 ∣ d₁) :
    3 ∣ e₁ := by
  sorry

/-- Subcase 2d: d₁ and e₁ are both odd, with e₁ ≥ 19.
    Use rotating colorings of intervals. -/
lemma subcase_2d {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (d₁ := d₁Param b (c - a + b)) (e₁ := e₁Param (c - a + b) d₁)
    (hd₁_odd : Odd d₁) (he₁_odd : Odd e₁) (he₁_large : 19 ≤ e₁) :
    HasPolychromColouring (Fin 3)
      ((transformedSet a b c).image (Int.cast : ℤ → ZMod (c - a + b))) := by
  sorry

/-- In Subcase 2d, d₁ ≥ 5. -/
lemma subcase_2d_d₁_ge_5 {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (d₁ := d₁Param b (c - a + b))
    (hd₁_not_div_3 : ¬ 3 ∣ d₁) (hMultiple : multipleCycleCase a b (c - a + b)) :
    5 ≤ d₁ := by
  sorry

/-- The rotation amounts rᵢ for Subcase 2d satisfy u ≤ rᵢ ≤ v + w = e₁ - u. -/
lemma subcase_2d_rotation_exists {e₁ d₁ : ℕ} (he₁ : 19 ≤ e₁) (hd₁ : 5 ≤ d₁)
    (he₁_odd : Odd e₁) :
    ∃ (u v w : ℕ) (r : Fin d₁ → ℕ),
      e₁ = u + v + w ∧ u ≥ v ∧ v ≥ w ∧ w ≥ u - 2 ∧
      (∀ i, u ≤ r i ∧ r i ≤ e₁ - u) ∧
      (Finset.univ.sum r) % e₁ = 0 := by
  sorry

/-- Main Case 2: Multiple cycle case is solvable. -/
lemma multipleCycle_solvable {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) (hc : 289 ≤ c)
    (hMultiple : multipleCycleCase a b (c - a + b)) :
    Accept a b c := by
  sorry

/-! ### Main Theorem -/

/-- Large case: For c ≥ 289, either single or multiple cycle case applies. -/
lemma large_case {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) (hc : 289 ≤ c) :
    Accept a b c := by
  by_cases h : singleCycleCase a b (c - a + b)
  · exact singleCycle_solvable ha hab hbc hgcd hc h
  · have : multipleCycleCase a b (c - a + b) := by
      unfold multipleCycleCase singleCycleCase at *
      omega
    exact multipleCycle_solvable ha hab hbc hgcd hc this

/-- Combining small and large cases for coprime triples. -/
lemma coprime_triple_polychrom {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (habc : a + b ≤ c) (hgcd : Nat.gcd a (Nat.gcd b c) = 1) :
    Accept a b c := by
  by_cases hc : c < 289
  · -- Small case: handled by allC_289
    exact suffices_nat 289 allC_289 a b c (by omega) (by omega) (by omega) (by omega)
      (by simp only [gcd_insert, id_eq, gcd_singleton, ← Int.coe_gcd, Int.gcd_natCast_natCast,
          Nat.cast_eq_one]; exact hgcd)
  · -- Large case
    exact large_case ha hab hbc hgcd (by omega)

/-- **Theorem 1**: Every set S ⊆ ℤ of 4 integers has a 3-polychromatic colouring.

This is the main result of the paper arXiv:1704.00042. The proof combines:
1. Reduction to canonical form `{0, a, b, c}` with `0 < a < b < c` and `gcd(a,b,c) = 1`
2. Computer verification for `c < 289` (via `allC_289`)
3. Case analysis (single cycle / multiple cycles) for `c ≥ 289`
-/
theorem theorem1 (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S := by
  -- Step 1: Reduce to {0, a, b, c} with 0 < a < b < c
  apply suffices_minimal
  apply suffices_triple
  intro a b c ha hab hbc
  -- Step 2: Use flip symmetry to assume a + b ≤ c
  apply suffices_flip 289
  intro a b c ha hab habc hcc
  -- Step 3: Use GCD reduction to assume gcd(a, b, c) = 1
  apply suffices_gcd 289
  intro a b c ha hab habc hcc hgcd
  -- Step 4: Convert to natural numbers and apply main lemma
  lift a to ℕ using by omega
  lift b to ℕ using by omega
  lift c to ℕ using by omega
  simp only [Int.coe_nat_pos] at ha
  simp only [Nat.cast_lt] at hab hbc
  simp only [Nat.cast_add, Nat.cast_le] at habc
  simp only [Nat.cast_lt] at hcc
  simp only [gcd_insert, id_eq, gcd_singleton, ← Int.coe_gcd, Int.gcd_natCast_natCast,
    Nat.cast_eq_one] at hgcd
  -- Step 5: Apply the combined case lemma
  exact coprime_triple_polychrom ha hab hbc habc hgcd
