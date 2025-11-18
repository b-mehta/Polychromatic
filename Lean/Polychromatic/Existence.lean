import Polychromatic.Colouring
import Polychromatic.LocalLemma
import Polychromatic.Compactness

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
  refine ⟨χ, fun x c ↦ ?_⟩
  obtain ⟨X, hxX, hX⟩ := hχ (x +ᵥ insert 0 S)
  obtain ⟨i, hi, hi'⟩ := hg X x (hxX (mem_vadd_finset.2 ⟨0, by simp⟩)) c
  refine ⟨i, hi, ?_⟩
  rw [hX _ _, hi']
  apply vadd_finset_subset_vadd_finset _ hi
  simp

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

-- lemma strictMonoOn {k : ℕ} :
--     StrictMonoOn (fun m : ℝ ↦ m ^ 2 * k * Real.exp (- m / k + 1)) (Set.Ici (2 * k)) := by
--   sorry

-- #exit

-- the function m^2 * k * (1-1/k)^m is decreasing in m for m ≥ -2 / ln(1 - 1/k) ≈ 2 k

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
  suffices 9 * k ^ 5 * Real.exp (- (3 * k) + 1) ≤ 1 by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ge_iff_le]
    field_simp
    linear_combination this
  sorry

-- 3 k log k + 2 k log log k + 16 e k

  -- have hm₀ : m ≠ 0 := ne_of_gt (hm.trans_lt' (by positivity))
  -- obtain rfl | rfl | hk : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  -- · simp [hm₀]
  -- · simp only [Nat.reducePow, Nat.reduceMul] at hm
  --   norm_num
  --   simp
  --   sorry
  -- apply condition_of_mul_exp_le ‹_› hm₀
  -- sorry


-- theorem exists_prime_aux (S : Finset ℕ) :
--     ∃ p : ℕ, p.Prime ∧ Set.InjOn (fun i : ℕ ↦ (i : ZMod p)) (S : Set ℕ) := by
--   obtain ⟨m, hm⟩ := S.bddAbove
--   obtain ⟨p, hp : m < p, hp'⟩ := Nat.exists_infinite_primes (m + 1)
--   use p, hp'
--   intro i hi j hj h
--   simp only at h
--   apply_fun ZMod.val at h
--   rwa [ZMod.val_natCast_of_lt, ZMod.val_natCast_of_lt] at h
--   · exact (hm hj).trans_lt hp
--   · exact (hm hi).trans_lt hp

-- theorem exists_prime {S : Finset ℤ} :
--     ∃ p : ℕ, p.Prime ∧ Set.InjOn (fun i : ℤ ↦ (i : ZMod p)) (S : Set ℤ) := by
--   obtain ⟨m, hm⟩ := S.bddBelow
--   generalize hS' : (-m) +ᵥ S = S'
--   have hS : S = m +ᵥ S' := by simp [← hS']
--   have hS'' : ∀ x ∈ S', 0 ≤ x := by
--     simp only [← hS', mem_vadd_finset, vadd_eq_add, forall_exists_index, and_imp,
--       forall_apply_eq_imp_iff₂]
--     intro i hi
--     have := hm hi
--     omega
--   lift S' to Finset ℕ using hS''
--   simpa [Set.InjOn, hS, mem_vadd_finset, mem_image, - coe_vadd_finset] using exists_prime_aux S'

-- theorem exists_colouring {k : ℕ} {S : Finset ℤ} (hm : 4 * k ^ 2 ≤ #S) :
--     HasPolychromColouring (Fin k) S := by
--   sorry
