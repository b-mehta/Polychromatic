import Polychromatic.Existence
import Polychromatic.PolychromNumber

/-!
# The Strauss Function

This file defines the Strauss function and studies its asymptotic behavior.

## Main definitions

* `straussFunction k`: The smallest `m` such that every set of size at least `m` has a
  `k`-polychromatic colouring.

## Main results

* `straussFunction_spec`: Sets of size at least `straussFunction k` have `k`-colourings.
* `straussFunction_le_of_forall`: Upper bounds on the Strauss function.
* `le_straussFunction_self`: `k ≤ straussFunction k` for all `k`.
* `straussFunction_isLittleO`: Asymptotically, `straussFunction k` is at most `(3 + o(1))k log k`.

## Implementation notes

The Strauss function is defined as `sInf` of a nonempty bounded set.
-/

open Finset

/-- The Strauss function: the smallest `m` such that every set of size at least `m` has a
`k`-polychromatic colouring. -/
-- ANCHOR: straussFunction
noncomputable def straussFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}
-- ANCHOR_END: straussFunction

@[simp] lemma straussFunction_zero : straussFunction 0 = 0 := by
  simp only [straussFunction, HasPolychromColouring, IsEmpty.exists_iff, imp_false, not_le,
    Nat.sInf_eq_zero, Set.mem_setOf_eq, not_lt_zero', forall_const, Set.eq_empty_iff_forall_notMem,
    not_forall, not_lt, false_or]
  exact fun n ↦ ⟨Finset.Ico 0 n, by simp⟩

private lemma straussFunction_nonempty {k : ℕ} (hk : k ≠ 0) :
    {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}.Nonempty :=
  ⟨3 * k ^ 2, fun _ hS ↦ exists_colouring_of_sq_le hk hS⟩

/-- Sets of size at least `straussFunction k` have `k`-colourings. -/
-- ANCHOR: straussFunction_spec
lemma straussFunction_spec {k : ℕ} (hk : k ≠ 0) (S : Finset ℤ)
    (hkS : straussFunction k ≤ #S) :
    HasPolychromColouring (Fin k) S :=
  Nat.sInf_mem (straussFunction_nonempty hk) S hkS
-- ANCHOR_END: straussFunction_spec

/-- Upper bounds on the Strauss function. -/
lemma straussFunction_le_of_forall {k m : ℕ}
    (h : ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m :=
  Nat.sInf_le h

lemma straussFunction_le_of_forall_eq {k m : ℕ}
    (h : ∀ S : Finset ℤ, #S = m → HasPolychromColouring (Fin k) S) :
    straussFunction k ≤ m :=
  straussFunction_le_of_forall fun _ hS ↦
    (exists_subset_card_eq hS).elim fun _ ⟨hS', hS'eq⟩ ↦ (h _ hS'eq).subset hS'

lemma straussFunction_pos {k : ℕ} (hk : k ≠ 0) : 0 < straussFunction k := by
  rw [pos_iff_ne_zero]; simpa using straussFunction_spec hk ∅

lemma lt_straussFunction_of_not_hasPolychromColouring {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : ¬ HasPolychromColouring (Fin k) S) :
    #S < straussFunction k := by
  by_contra!; exact hkS (straussFunction_spec hk S this)

lemma lt_straussFunction_of_polychromNumber {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : polychromNumber S < k) :
    #S < straussFunction k :=
  lt_straussFunction_of_not_hasPolychromColouring hk (by
    rw [← le_polychromNumber_iff_hasPolychromColouring hk]; simpa)

/-- `k ≤ straussFunction k` for all `k`. -/
-- ANCHOR: le_straussFunction_self
lemma le_straussFunction_self {k : ℕ} :
    k ≤ straussFunction k := by
-- ANCHOR_END: le_straussFunction_self
  obtain rfl | hk := eq_or_ne k 0
  · simp
  have hS : #(Finset.Ico (0 : ℤ) (↑k - 1)) = k - 1 := by simp
  have : polychromNumber (Finset.Ico (0 : ℤ) (k - 1)) < k := by
    grind [polychromNumber_le_card]
  grind [lt_straussFunction_of_polychromNumber hk this]

@[simp] lemma straussFunction_one : straussFunction 1 = 1 :=
  le_antisymm
    (straussFunction_le_of_forall fun S hS ↦
      hasPolychromColouring_fin_of_le (by simp) (one_le_polychromNumber (card_pos.mp hS)))
    (straussFunction_pos (by simp))

@[simp] lemma straussFunction_two : straussFunction 2 = 2 :=
  le_antisymm
    (straussFunction_le_of_forall_eq fun S hS ↦
      hasPolychromColouring_fin_of_le (by simp)
        (by rw [polychromNumber_eq_card_of_card_le_two hS.le, hS]))
    le_straussFunction_self

lemma four_le_straussFunction_three : 4 ≤ straussFunction 3 := by
  suffices #({0, 1, 3} : Finset ℤ) < straussFunction 3 by simpa using this
  exact lt_straussFunction_of_polychromNumber (by simp) (by rw [polychromNumber_three_eq_two]; simp)

-- ANCHOR: straussFunction_le_of_forall_three_mul_sq
lemma straussFunction_le_of_forall_three_mul_sq {k : ℕ} :
    straussFunction k ≤ 3 * k ^ 2 := by
-- ANCHOR_END: straussFunction_le_of_forall_three_mul_sq
  obtain rfl | hk := eq_or_ne k 0
  · simp
  exact straussFunction_le_of_forall fun _ hS ↦ exists_colouring_of_sq_le hk hS

lemma straussFunction_le_of_forall_mBound {k : ℕ} (hk : 4 ≤ k) : straussFunction k ≤ mBound k :=
  straussFunction_le_of_forall fun _ ↦ hasPolychromColouring_mBound hk

open Asymptotics Filter

/-- Asymptotically, `straussFunction k` is at most `(3 + o(1))k log k`. -/
-- ANCHOR: straussFunction_isLittleO
lemma straussFunction_isLittleO :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 4,
      straussFunction k ≤ (3 + f k) * k * Real.log k := by
-- ANCHOR_END: straussFunction_isLittleO
  obtain ⟨f, hf, hfbound⟩ := mBound_isLittleO
  exact ⟨f, hf, fun k hk ↦ by
    grw [straussFunction_le_of_forall_mBound hk]
    exact hfbound _ (by grind)⟩

lemma straussFunction_le_of_forall_mul_log {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, straussFunction k ≤ (3 + ε) * k * Real.log k := by
  obtain ⟨f, hf, hfbound⟩ := straussFunction_isLittleO
  rw [isLittleO_one_iff] at hf
  filter_upwards [hf.eventually_le_const hε, eventually_ge_atTop 4] with k hk hk4
  grw [hfbound k hk4, hk]
