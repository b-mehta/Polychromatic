import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Polychromatic.Colouring
import Polychromatic.Compactness
import Polychromatic.LocalLemma

/-!
# Existence of Polychromatic Colourings

This file proves existence results for polychromatic colourings using the
Lovász Local Lemma and probabilistic methods.

## Main definitions

* `polychromColouringBound k m`: A condition on `k` (number of colours) and `m` (size of set)
  that guarantees the existence of a polychromatic colouring.
* `mBound k`: An asymptotically optimal bound on the set size needed for `k` colours,
  approximately `3k log k`.

## Main results

* `exists_colouring_of_sq_le`: For sets of size at least `3k²`, a `k`-colouring exists.
* `hasPolychromColouring_mBound`: For `k ≥ 4` and sets of size at least `mBound k`,
  a `k`-colouring exists.
* `exists_colouring_asymptotic`: Asymptotically, sets of size `(3 + ε)k log k` have
  `k`-colourings for sufficiently large `k`.

## Main techniques

The proofs use:
1. The symmetric Lovász Local Lemma for uniform probability bounds
2. The Rado selection principle for extending finite colourings to infinite ones
3. Analysis of the probability that a random colouring fails to be polychromatic

## References

* The probabilistic method follows standard applications of the Lovász Local Lemma
  to colouring problems.
-/

open Finset

open Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

-- tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
open MeasureTheory ProbabilityTheory

lemma standardCondition_lovasz {k : ℕ} {S X : Finset G} (hk : k ≠ 0) :
    standardCondition
      (Measure.pi (fun _ ↦ uniformOn Set.univ))
      (fun x : X ↦ {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c})
      (fun x : X ↦ X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)) := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 (by omega)
  set add : X → S → X + S := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  set D : X → Finset (X + S) := fun x ↦ S.attach.image (fun s ↦ add x s)
  refine standardCondition_of _ D ?_ (by fun_prop)
    (iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)) ?_
  · simp only [ne_eq, mem_erase, mem_sub, mem_filter, mem_attach, true_and, not_and, not_exists,
      disjoint_left, mem_image, Subtype.exists, forall_exists_index, Subtype.forall, mem_add,
      Subtype.mk.injEq, and_imp, D, add]
    rintro x₁ hx₁ x₂ hx₂ hne hS _ x₃ hx₃ s₁ hs₁ rfl s₂ hs₂ h s₃ hs₃ h'
    exact hS (by grind) s₂ hs₂ s₃ hs₃ (by grind)
  · rintro x
    refine ⟨{χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c},
      MeasurableSet.of_discrete, ?_, rfl⟩
    simp only [DependsOn, coe_image, coe_attach, Set.image_univ, Set.mem_range, Subtype.exists,
      forall_exists_index, Subtype.forall, Subtype.mk.injEq, Set.mem_setOf_eq, eq_iff_iff, D,
      add]
    intro χ₁ χ₂ h
    peel with c s hs
    rw [h _ _ _ hs rfl]

lemma prob_bad_event {k m : ℕ} {S X : Finset G} {x : X} (hm : #S = m) (hk : k ≠ 0) :
    (Measure.pi (fun _ ↦ uniformOn Set.univ) : Measure (X + S → Fin k)).real
      {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c} ≤
        k * (1 - (k : ℝ)⁻¹) ^ m := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 (by omega)
  set add : X → S → X + S := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  set P : Measure (X + S → Fin k) := Measure.pi (fun _ ↦ uniformOn Set.univ)
  have : {χ : X + S → Fin k | ∃ c, ∀ s : S, χ ⟨x + s, add_mem_add x.2 s.2⟩ ≠ c} =
      ⋃ c : Fin k, (add x '' Set.univ : Set (X + S)).pi fun _ ↦ {c}ᶜ := by
    ext χ
    simp only [ne_eq, Subtype.forall, Set.mem_setOf_eq, Set.image_univ, Set.mem_iUnion,
      Set.mem_pi, Set.mem_range, Subtype.exists, Set.mem_compl_iff, Set.mem_singleton_iff,
      forall_exists_index, Subtype.mk.injEq, add]
    peel with c
    constructor
    · rintro h y hy s hs rfl
      exact h _ hs
    · rintro h s hs
      exact h _ _ _ hs rfl
  calc
    _ = P.real (⋃ c : Fin k, (add x '' Set.univ).pi fun _ ↦ {c}ᶜ) := by rw [this]
    _ ≤ ∑ c, P.real ((add x '' Set.univ).pi fun _ ↦ {c}ᶜ) := measureReal_iUnion_fintype_le _
    _ = ∑ c, P.real ((univ.image (add x) : Set (X + S)).pi fun _ ↦ {c}ᶜ) := by simp
    _ = ∑ c : Fin k, ((Measure.count {c}ᶜ).toReal / k) ^ #(S.attach.image (add x)) := by
      simp only [Measure.real_def, P, pi_pi']
      simp [uniformOn_univ]
    _ = ∑ c : Fin k, ((k - 1 : ℝ) / k) ^ #S := by
      congr! with c hc
      · have : ({c}ᶜ : Set (Fin k)) = ({c}ᶜ : Finset (Fin k)) := by simp
        rw [this, Measure.count_apply_finset, ENNReal.toReal_natCast, Finset.card_compl,
          Fintype.card_fin, card_singleton, Nat.cast_sub (by cutsat), Nat.cast_one]
      · rw [card_image_of_injective, card_attach]
        simp [Function.Injective, add]
    _ = k * (1 - (k : ℝ)⁻¹) ^ m := by simp [sub_div, field, hk, hm]

lemma card_neighbour {m : ℕ} {S X : Finset G} (hm : #S = m) {x : X} :
    #(X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)) ≤ m * (m - 1) := by
  calc
    #({i ∈ X.attach | x.1 - i.1 ∈ (S - S).erase 0}) = #({i ∈ X | ↑x - i ∈ (S - S).erase 0}) := by
      rw [filter_attach (fun i ↦ x.1 - i ∈ (S - S).erase 0), card_map, card_attach]
    _ ≤ #(((S - S).erase 0).image (x.1 - ·)) := by
      apply card_le_card
      intro j
      simp only [mem_filter, mem_image, and_imp]
      intro i hi
      exact ⟨_, hi, by grind⟩
    _ ≤ #((S - S).erase 0) := card_image_le
    _ ≤ #S * (#S - 1) := card_sub_erase_zero_le
    _ = m * (m - 1) := by simp [hm]

lemma nonempty_of_uniformOn_apply_pos' {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}
    (h : 0 < uniformOn s t) (hs : MeasurableSet s) :
    (s ∩ t).Nonempty := by
  rw [uniformOn, cond_apply hs] at h
  have : Measure.count (s ∩ t) ≠ 0 := by contrapose! h; simp [h]
  rwa [Measure.count_ne_zero_iff] at this

lemma nonempty_of_uniformOn_apply_pos {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s t : Set Ω} (h : 0 < uniformOn s t) :
    (s ∩ t).Nonempty := by
  have hs_fin : s.Finite := finite_of_uniformOn_ne_zero h.ne'
  exact nonempty_of_uniformOn_apply_pos' h (hs_fin.measurableSet)

/-- A condition on `k` (number of colours) and `m` (size of set) that guarantees the existence
of a polychromatic colouring. -/
def polychromColouringBound (k m : ℕ) : Prop :=
  Real.exp 1 * (m * (m - 1) + 1) * k * (1 - (k : ℝ)⁻¹) ^ m ≤ 1

lemma exists_finite_of_le {k m : ℕ} (X : Finset G) {S : Finset G} (hm : #S = m)
    (hm₂ : 2 ≤ m) (hk : k ≠ 0) (hkm : polychromColouringBound k m) :
    ∃ χ : G → Fin k, ∀ x ∈ X, ∀ c : Fin k, ∃ i ∈ x +ᵥ S, χ i = c := by
  let Y : Finset G := X + S
  have : NeZero k := ⟨hk⟩
  let add : X → S → Y := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  let A (x : X) : Set (Y → Fin k) := {χ | ∃ c, ∀ s, χ (add x s) ≠ c}
  let D : X → Finset Y := fun x ↦ S.attach.image (fun s ↦ add x s)
  let N : X → Finset X := fun x ↦ X.attach.filter (fun i ↦ x.1 - i.1 ∈ (S - S).erase 0)
  let P : Measure (Y → Fin k) := Measure.pi fun _ ↦ uniformOn Set.univ
  have hP : P = uniformOn Set.univ := by simp only [P, ← uniformOn_pi, Set.pi_univ]
  have hPAN : standardCondition P A N := standardCondition_lovasz hk
  let p : ℝ := k * (1 - (k : ℝ)⁻¹) ^ m
  have hp (x : X) : P.real (A x) ≤ p := prob_bad_event hm hk
  have hp₀ : 0 ≤ p := by
    apply mul_nonneg (by positivity) (pow_nonneg _ _)
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; cutsat)
  have hm₀ : m * (m - 1) ≠ 0 := by
    have : 0 < m * (m - 1) := mul_pos (by grind) (by grind)
    exact this.ne'
  have :  0 < P.real (⋂ i, (A i)ᶜ) := by
    apply symmetricLocalLemma (fun i ↦ .of_discrete) hm₀ (p := p)
      (d := m * (m - 1)) (lopsidedCondition_of_standardCondition hPAN) hp
      (fun i ↦ card_neighbour hm)
    calc
      Real.exp 1 * p * ((m * (m - 1) : ℕ) + 1) = Real.exp 1 * p * (m * (m - 1) + 1) := by
          have : 1 ≤ m := by cutsat
          simp [this]
      _ = _ := by simp only [p]; ring
      _ ≤ _ := hkm
  have : (⋂ i, (A i)ᶜ).Nonempty := by
    rw [hP, Measure.real_def, ENNReal.toReal_pos_iff] at this
    simpa using nonempty_of_uniformOn_apply_pos this.1
  obtain ⟨χ, hχ⟩ := this
  refine ⟨fun g ↦ if hg : g ∈ Y then χ ⟨g, hg⟩ else 0, ?_⟩
  intro x hx c
  simp only [ne_eq, Subtype.forall, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists,
    not_forall, Decidable.not_not, A, add] at hχ
  obtain ⟨s, hs, hc⟩ := hχ x hx c
  refine ⟨x + s, ?_⟩
  simp [add_mem_add, hx, hs, Y, hc]

lemma exists_of_le {k m : ℕ} {S : Finset G} (hm : #S = m) (hm₂ : 2 ≤ m) (hk : k ≠ 0)
    (hkm : polychromColouringBound k m) :
    HasPolychromColouring (Fin k) S := by
  have (X : Finset G) : ∃ χ : G → Fin k, ∀ x ∈ X, ∀ (c : Fin k), ∃ i ∈ x +ᵥ S, χ i = c :=
    exists_finite_of_le X hm hm₂ hk hkm
  choose g hg using this
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (α := G) (β := fun _ ↦ Fin k) g
  refine ⟨χ, ?_⟩
  rw [isPolychrom_iff]
  intro x c
  obtain ⟨X, hxX, hX⟩ := hχ (x +ᵥ insert 0 S)
  obtain ⟨i, hi, hi'⟩ := hg X x (hxX (mem_vadd_finset.2 ⟨0, by simp⟩)) c
  refine ⟨i, hi, ?_⟩
  rw [hX _ _, hi']
  apply vadd_finset_subset_vadd_finset _ hi
  simp

open Real

lemma condition_of_mul_exp_le {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    (hm : m ^ 2 * k * Real.exp (- m / k + 1) ≤ 1) :
    polychromColouringBound k m := by
  have : 0 ≤ 1 - (k : ℝ)⁻¹ := by
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; cutsat)
  calc
    _ ≤ Real.exp 1 * m ^ 2 * k * (1 - (k : ℝ)⁻¹) ^ m := by
      gcongr
      have : (1 : ℝ) ≤ m := by simp; cutsat
      linear_combination this
    _ = Real.exp 1 * m ^ 2 * k * ((-k : ℝ)⁻¹ + 1) ^ m := by ring
    _ ≤ Real.exp 1 * m ^ 2 * k * Real.exp ((- k : ℝ)⁻¹) ^ m := by
      gcongr
      · simpa
      exact Real.add_one_le_exp _
    _ = m ^ 2 * k * (Real.exp 1 * Real.exp (- m / k)) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    _ = m ^ 2 * k * Real.exp (- m / k + 1) := by
      grind [Real.exp_add]
    _ ≤ 1 := hm

lemma polychromColouringBound_succ {k m : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ m + 1)
    (hkm : polychromColouringBound k m) :
    polychromColouringBound k (m + 1) := by
  have : 0 ≤ 1 - (k : ℝ)⁻¹ := by
    simp only [sub_nonneg]
    apply inv_le_one_of_one_le₀ (by simp; cutsat)
  rw [polychromColouringBound, mul_right_comm _ _ (k : ℝ), mul_assoc (_ * _)] at hkm ⊢
  refine hkm.trans' ?_
  rw [pow_succ', ← mul_assoc (_ + 1 : ℝ), Nat.cast_add_one]
  gcongr _ * (?_ * _)
  simp only [add_sub_cancel_right, fieldLe]
  rify at h
  linear_combination (m : ℝ) * h

lemma polychromColouringBound_mono {k m m' : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ m + 1)
    (hm' : m ≤ m') (hkm : polychromColouringBound k m) :
    polychromColouringBound k m' := by
  have : MonotoneOn (polychromColouringBound k) {m | 2 * k - 1 ≤ m} :=
    monotoneOn_nat_Ici_of_le_succ fun x hx ↦ polychromColouringBound_succ hk (by cutsat)
  exact this (by grind) (by grind) hm' hkm

lemma polychromColouringBound_zero {m : ℕ} : polychromColouringBound 0 m := by
  simp [polychromColouringBound]

lemma polychromColouringBound_one {m : ℕ} (hm : m ≠ 0) : polychromColouringBound 1 m := by
  simp [polychromColouringBound, hm]

-- 9 is optimal for the LLL bound, but likely not optimal for polychromatic colourings
lemma polychromColouringBound_two_of_ge {m : ℕ} (hm : 9 ≤ m) : polychromColouringBound 2 m := by
  apply polychromColouringBound_mono (by norm_num) (by norm_num) hm
  grw [polychromColouringBound, Real.exp_one_lt_d9]
  norm_num

lemma condition_of_mul_sq {k m : ℕ} (hm : 3 * k ^ 2 ≤ m) :
    polychromColouringBound k m := by
  obtain rfl | rfl | rfl | hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · exact polychromColouringBound_zero
  · exact polychromColouringBound_one (by cutsat)
  · exact polychromColouringBound_two_of_ge (by cutsat)
  apply polychromColouringBound_mono (by cutsat) _ hm
  swap
  · linear_combination (3 * k + 7) * hk
  apply condition_of_mul_exp_le (by cutsat) (ne_of_gt <| by linear_combination ((3 * k + 9) * hk))
  have hk₀ : k ≠ 0 := by omega
  let g (k : ℕ) : ℝ := k ^ 5 * Real.exp (-(3 * k) + 1)
  suffices 9 * g k ≤ 1 by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ge_iff_le]
    field_simp
    linear_combination this
  have : 9 * g 3 ≤ 1 := by
    suffices 2187 * Real.exp (-1) ^ 8 ≤ 1 by
      rw [← Real.exp_nat_mul] at this
      norm_num [g, ← mul_assoc]
      norm_num at this
      exact this
    grw [Real.exp_neg_one_lt_d9]
    norm_num
  suffices AntitoneOn g {x | 3 ≤ x} by
    grw [this (by simp) hk hk]
    assumption
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  simp only [g]
  suffices (1 / n + 1) ^ 5 ≤ Real.exp 3 by
    simp only [Nat.cast_add_one, mul_add_one, neg_add_rev, Real.exp_add, ← mul_assoc, Real.exp_neg]
    gcongr ?_ * _ * _
    grw [← this]
    rw [← inv_pow, ← mul_pow]
    gcongr
    simp [field, add_comm]
  grw [Real.add_one_le_exp, ← Real.exp_nat_mul, hn]
  gcongr
  norm_num

/-- For sets of size at least `3k²`, a `k`-colouring exists. -/
theorem exists_colouring_of_sq_le {S : Finset G} {k : ℕ} (hk : k ≠ 0) (hm : 3 * k ^ 2 ≤ #S) :
    HasPolychromColouring (Fin k) S := by
  refine exists_of_le rfl ?_ hk (condition_of_mul_sq hm)
  have : 1 ≤ k := by cutsat
  grw [← hm, ← this]
  simp

/-- An asymptotically optimal bound on the set size needed for `k` colours,
approximately `3k log k`. -/
noncomputable def mBound (k : ℕ) : ℕ :=
  ⌈k * (3 * log k + (2 * log (log k) + 5.2))⌉₊

private lemma mBound_pos_aux {k : ℕ} : 0 < 2 * log (log k) + 4.2 := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · norm_num
  · norm_num
  suffices -2 ≤ log (log k) by linear_combination 2 * this
  grw [le_log_iff_exp_le (log_pos (by simpa)), exp_neg, ← exp_one_rpow, ← hk, Nat.cast_ofNat,
    ← exp_one_gt_d9, ← log_two_gt_d9]
  norm_num

@[simp] lemma mBound_zero : mBound 0 = 0 := by simp [mBound]
@[simp] lemma mBound_one : mBound 1 = 6 := by norm_num [mBound]

lemma le_mBound {k : ℕ} : 3 * k * log k ≤ mBound k := by
  grw [mBound, ← Nat.le_ceil]
  have : (0 : ℝ) ≤ k := by positivity
  linear_combination mBound_pos_aux * (k : ℝ) + this

lemma linear_le_mBound {k : ℕ} : 2 * k ≤ mBound k := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · simp
  · simp
  rify
  grw [← le_mBound]
  have : 2 / 3 ≤ log k := by grw [← hk, Nat.cast_two, ← log_two_gt_d9]; norm_num
  linear_combination 3 * k * this

@[simp] lemma mBound_pos {k : ℕ} (hk : k ≠ 0) : 0 < mBound k := by
  grw [← linear_le_mBound]; positivity
@[simp] lemma mBound_ne_zero {k : ℕ} (hk : k ≠ 0) : mBound k ≠ 0 := by
  grind [mBound_pos]

lemma ceil_nat_mul_le {k : ℕ} {x : ℝ} : ⌈k * x⌉₊ ≤ k * ⌈x⌉₊ := by
  grw [Nat.ceil_le, Nat.cast_mul, ← Nat.le_ceil x]

lemma mBound_le_helper {k : ℕ} :
    mBound k ≤ k * (3 * log k + (2 * log (log k) + 6.2)) := by
  obtain rfl | rfl | hk : k = 0 ∨ k = 1 ∨ 2 ≤ k := by grind
  · simp
  · norm_num
  grw [mBound, ceil_nat_mul_le, Nat.cast_mul, Nat.ceil_lt_add_one _]
  · linear_combination
  apply add_nonneg
  · positivity
  linear_combination mBound_pos_aux

lemma mBound_le_weak {k : ℕ} (hk : 4 ≤ k) : mBound k ≤ 8 * k * log k := by
  suffices 2 * log (log k) + 6.2 ≤ 5 * log k by
    linear_combination mBound_le_helper (k := k) + (k : ℝ) * this
  suffices ∀ x, 1.37 < x → 2 * log x + 6.2 ≤ 5 * x by
    apply this (log k)
    have : 1.37 < (2 : ℕ) * log 2 := by linear_combination 2 * log_two_gt_d9
    refine this.trans_le ?_
    grw [← hk, ← log_pow]
    norm_num
  intro x hx
  suffices StrictMonoOn (fun x ↦ x * 5 - 2 * log x) (Set.Ici 1.37) by
    have h₁ : log 1.37 ≤ 13 / 40 := by
      rw [log_le_iff_le_exp (by norm_num)]
      grw [← quadratic_le_exp_of_nonneg (by norm_num)]
      norm_num
    have h₂ := this (by simp) (by simp [hx.le]) hx
    linear_combination 2 * h₁ + h₂
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fun x ↦ 5 - 2 * x⁻¹) (convex_Ici _)
  · apply ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) _)
    apply ContinuousOn.log (by fun_prop)
    simp only [Set.mem_Ici, ne_eq]
    intro x hx
    positivity
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    apply HasDerivWithinAt.sub
    · apply (hasDerivAt_mul_const _).hasDerivWithinAt
    apply HasDerivWithinAt.const_mul
    apply (hasDerivAt_log (by positivity)).hasDerivWithinAt
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, sub_pos]
    intro y hy
    grw [← hy]
    norm_num

open Asymptotics Filter Topology

lemma mBound_isLittleO :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 2, mBound k ≤ (3 + f k) * k * log k := by
  refine ⟨fun k ↦ (2 * log (log k) + 6.2) / log k, ?_, ?_⟩
  · rw [isLittleO_one_iff]
    suffices Tendsto (fun x : ℝ ↦ (2 * log x + 6.2) / x) atTop (𝓝 0) from
      this.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have : Tendsto (fun x ↦ log x / x) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
    simp only [add_div, mul_div_assoc, div_eq_mul_inv (6.2 : ℝ)]
    simpa using (this.const_mul 2).add (tendsto_inv_atTop_zero.const_mul 6.2)
  intro k hk
  have hk' : 0 < log k := log_pos (by simp; cutsat)
  calc
    (mBound k : ℝ) ≤ k * (3 * log k + (2 * log (log k) + 6.2)) := mBound_le_helper
    _ = (3 + (2 * log (log k) + 6.2) / log k) * k * log k := by simp [field]

lemma polychromColouringBound_mBound {k : ℕ} (hk : 4 ≤ k) :
    polychromColouringBound k (mBound k) := by
  have hk' : k ≠ 0 := by omega
  have hk'' : 0 < log k := log_pos (by simp; cutsat)
  apply condition_of_mul_exp_le hk' (mBound_ne_zero hk')
  calc
    mBound k ^ 2 * k * exp (- mBound k / k + 1) ≤
        (8 * k * log k) ^ 2 * k * exp (- mBound k / k + 1) := by
      gcongr
      exact mBound_le_weak hk
    _ ≤ (8 * k * log k) ^ 2 * k * exp (- (3 * log k + (2 * log (log k) + 5.2)) + 1) := by
      grw [mBound, ← Nat.le_ceil, neg_div, mul_div_cancel_left₀ _ (by positivity)]
    _ = 2 ^ 6 * k ^ 3 * log k ^ 2 * exp (log k * (-3) + log (log k) * (-2) + - 4.2) := by
      ring_nf
    _ = 2 ^ 6 * exp (-4.2) := by
      rw [exp_add, exp_add, ← rpow_def_of_pos (by positivity),
        ← rpow_def_of_pos (by positivity)]
      simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat]
      simp [field]
    _ ≤ 1 := by
      grw [← log_le_log_iff (by positivity) (by positivity),
        log_mul (by positivity) (by positivity), log_exp, log_one, log_pow, log_two_lt_d9]
      norm_num

/-- For `k ≥ 4` and sets of size at least `mBound k`, a `k`-colouring exists. -/
lemma hasPolychromColouring_mBound {S : Finset G} {k : ℕ} (hk : 4 ≤ k) (hS : mBound k ≤ #S):
    HasPolychromColouring (Fin k) S := by
  have h2S : 2 ≤ #S := by
    grw [← hS, ← linear_le_mBound, ← hk]
    norm_num
  apply exists_of_le rfl (mod_cast h2S) (by omega)
  apply polychromColouringBound_mono (by cutsat) _ hS (polychromColouringBound_mBound hk)
  · linear_combination linear_le_mBound (k := k)

/-- Asymptotically, sets of size `(3 + ε)k log k` have `k`-colourings for sufficiently large `k`. -/
theorem exists_colouring_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset G, (3 + ε) * k * log k ≤ #S →
      HasPolychromColouring (Fin k) S := by
  obtain ⟨f, hf₁, hf₂⟩ := mBound_isLittleO
  rw [isLittleO_one_iff] at hf₁
  filter_upwards [hf₁.eventually_le_const hε, eventually_ge_atTop 4] with k hk hk4 S hS
  apply hasPolychromColouring_mBound hk4
  rify
  grw [hf₂ k (by cutsat), hk, hS]
