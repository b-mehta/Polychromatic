import Polychromatic.FourThree.Combi.BlockColour
import Polychromatic.FourThree.Combi.CaseOne
import Polychromatic.FourThree.Combi.CaseTwo

/-!
# Combinatorial case analysis for the polychromatic coloring theorem

This file contains the final assembly for the polychromatic coloring theorem
for 4-element sets, importing the three components of the proof:

- `Combi.BlockColour` — block colouring infrastructure, Table 1, and shared utilities
- `Combi.CaseOne` — Case 1 (single cycle)
- `Combi.CaseTwo` — Case 2 (multiple cycles)

## Main results

- `normal_bit` — **the main theorem**: every normalized 4-element set admits a
  3-polychromatic coloring. This is the entry point used by `Main.lean`.

## Proof structure

Following the reduction in `Main.lean`, we assume the set $S = \{0, a, b, c\}$ is normalized
such that $0 < a < b < c$, $a + b \le c$, $c \ge 289$, and $\gcd(a, b, c) = 1$.
The proof works in the cyclic group $\mathbb{Z}_m$ where $m = c - a + b$.
As shown in §4 of the paper, the polychromaticity of $S$ in $\mathbb{Z}$ follows from
its polychromaticity in $\mathbb{Z}_m$.

Let $d_1 = \gcd(b, m)$ and $d_2 = \gcd(b{-}a, m)$. The proof dispatches on whether
one of these GCDs equals 1 (so the corresponding element generates all of
$\mathbb{Z}_m$) or both are greater than 1 (so $\mathbb{Z}_m$ decomposes into
shorter cycles):

- `main_case_one` — **Case 1: Single Cycle (§4.1).**
  Applies when $\min(d_1, d_2) = 1$. The set reduces to $\{0,1,g,g{+}1\}$ via an
  affine transformation (`exists_g_of_coprime`). Subcases by the gap parameter $g$:
  - `case_one_small_g` — **(1a)** $g \in \{2,3,4\}$, via Table 1 block colorings.
  - `case_one_interval` — **(1b)** General $g$, via interval coloring.
  - `case_one_residues` — **(1c)** $3 \nmid m$, via multiplication by 3.
  - `case_one_divisible` — **(1d)** $3 \mid m$, via explicit periodic colorings.

- `main_case_two` — **Case 2: Multiple Cycles (§4.2).**
  Applies when both $d_1, d_2 > 1$. Setting $e_1 = m/d_1$, we use the isomorphism
  $\mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \cong \mathbb{Z}_m$ to define colorings
  cycle-by-cycle. Subcases by the parity of $d_1$ and $e_1$:
  - `case_two_e1_even` — **(2a)** $e_1$ even: parity-based alternation.
  - `case_two_d1_even_e1_odd` — **(2b)** $d_1$ even, $e_1$ odd: alternation with fixup.
  - `case_two_odd_small` — **(2c)** Both odd, $e_1 \le 17$: shifted periodic colorings.
  - `case2d_coloring_works` — **(2d)** Both odd, $e_1 \ge 19$: rotating interval patterns.
-/

open Finset Pointwise

/-! ## Assembly: connecting ZMod m back to ℤ

The remaining lemmas are the glue between the Case 1/Case 2 analysis in $\mathbb{Z}_m$
and the final statement over $\mathbb{Z}$, culminating in `normal_bit`.
-/

section Assembly

/-- Auxiliary: the set zmod_set m a b has 4 elements when 0 < a < b and 2b - a < m. -/
lemma zmod_set_card_eq_four {a b : ℤ} {m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbm : 2 * b - a < ↑m) :
    (zmod_set m a b).card = 4 := by
  unfold zmod_set
  -- Helper: two integers in [0, m) that cast to the same ZMod m element must be equal
  have hne : ∀ x y : ℤ, 0 ≤ x → x < ↑m → 0 ≤ y → y < ↑m → x ≠ y →
      (x : ZMod m) ≠ (y : ZMod m) := fun _ _ hx1 hx2 hy1 hy2 hxy h =>
    hxy (by rwa [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hx1 hx2,
                  Int.emod_eq_of_lt hy1 hy2] at h)
  have ne01 := hne 0 (b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne02 := hne 0 b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne03 := hne 0 (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne12 := hne (b - a) b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne13 := hne (b - a) (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne23 := hne b (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  simp only [image_insert, image_singleton]
  grind

/-- Auxiliary: the coprimality gcd(d₁, d₂) = 1 follows from gcd(a, b, c) = 1. -/
lemma gcd_coprime_of_gcd_abc {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (hgcd : Finset.gcd {a, b, c} id = 1) :
    (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1 := by
  set d := (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) with hd_def
  -- d divides b, (b-a), and m (lifted to ℤ)
  have hd_b : (d : ℤ) ∣ b := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_left _ _))
  have hd_m : (d : ℤ) ∣ ↑m := Int.natCast_dvd_natCast.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_right _ _))
  have hd_ba : (d : ℤ) ∣ (b - a) := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_right (Nat.gcd _ _) _).trans (Nat.gcd_dvd_left _ _))
  -- d | a and d | c follow from d | b, d | (b-a), d | m
  have hd_a : (d : ℤ) ∣ a := by
    have : a = b - (b - a) := by ring
    rw [this]
    exact dvd_sub hd_b hd_ba
  have hd_c : (d : ℤ) ∣ c := by
    have : (c : ℤ) = ↑m - b + a := by grind
    rw [this]
    exact dvd_add (dvd_sub hd_m hd_b) hd_a
  have hd_dvd_gcd : (d : ℤ) ∣ Finset.gcd {a, b, c} id :=
    Finset.dvd_gcd (fun x hx => by
      grind)
  rw [hgcd] at hd_dvd_gcd
  exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd_dvd_gcd)

/-- Auxiliary: lifts polychromaticity from ZMod m back to ℤ, combining the
    homomorphism ℤ → ZMod m (Lemma 12(ii)) with `polychromNumber_zmod`. -/
lemma hasPolychromColouring_of_zmod_set {a b c : ℤ} {m : ℕ}
    (hm_eq : (m : ℤ) = c - a + b)
    (h : HasPolychromColouring (Fin 3) (zmod_set m a b)) :
    HasPolychromColouring (Fin 3) ({0, a, b, c} : Finset ℤ) := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod m))
  change HasPolychromColouring (Fin 3) (({0, a, b, c} : Finset ℤ).image (Int.cast : ℤ → ZMod m))
  apply hasPolychromColouring_fin_of_le (by simp)
  rw [polychromNumber_zmod hm_eq]
  exact le_polychromNumber h

/--
**Main theorem of this file.** Every 4-element set $\{0, a, b, c\}$ satisfying the
normalization conditions ($0 < a < b$, $a + b \le c$, $c \ge 289$, $\gcd(a, b, c) = 1$)
admits a 3-polychromatic coloring.

This is the entry point used by `Main.lean` to handle the large-c case. The proof
dispatches to `main_case_one` or `main_case_two` based on
$\min(\gcd(b, m), \gcd(b{-}a, m))$.
-/
theorem normal_bit :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → 289 ≤ c → Finset.gcd {a, b, c} id = 1 →
          HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hc hgcd
  set m := (c - a + b).toNat
  have hm_eq : (m : ℤ) = c - a + b := Int.toNat_of_nonneg (by grind)
  have hm_pos : 0 < m := by grind
  have hcard := zmod_set_card_eq_four ha hab (by linarith)
  apply hasPolychromColouring_of_zmod_set hm_eq
  set d₁ := Nat.gcd b.natAbs m
  set d₂ := Nat.gcd (b - a).natAbs m
  by_cases hmin : min d₁ d₂ = 1
  · apply main_case_one m a b (by grind) hcard
    grind
  · have : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    exact main_case_two (by grind) (gcd_coprime_of_gcd_abc hm_eq hgcd) (by grind)

end Assembly
