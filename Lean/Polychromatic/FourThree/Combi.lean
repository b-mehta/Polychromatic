import Polychromatic.FourThree.Combi.BlockColour
import Polychromatic.FourThree.Combi.CaseOne
import Polychromatic.FourThree.Combi.CaseTwo

/-!
# Combinatorial case analysis — assembly

This file re-exports the three components of the combinatorial argument
(`BlockColor`, `CaseOne`, `CaseTwo`) and contains the final assembly
that connects the $\mathbb{Z}_m$ analysis back to $\mathbb{Z}$.
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
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · rw [mem_singleton]; exact ne23
  · simp only [mem_insert, mem_singleton]; push_neg; exact ⟨ne12, ne13⟩
  · simp only [mem_insert, mem_singleton]; push_neg; exact ⟨ne01, ne02, ne03⟩

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
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hd_a
      · exact hd_b
      · exact hd_c)
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
    have hd₁_pos : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    rcases min_choice d₁ d₂ with h | h <;> rw [h] at hmin <;> [left; right] <;> grind
  · have : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    exact main_case_two m a b (by grind) (gcd_coprime_of_gcd_abc hm_eq hgcd) (by grind)

end Assembly
