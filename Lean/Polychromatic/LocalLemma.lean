import Mathlib

open MeasureTheory ProbabilityTheory Measure

variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}

section

open MeasurableSpace Measure

variable {s : Set Ω} {t t' : Set (Set Ω)}

def IndepFrom (s : Set Ω) (t : Set (Set Ω)) (P : Measure Ω) : Prop :=
  Indep (generateFrom {s}) (generateFrom t) P

lemma indepFrom_iff_indepSets {P : Measure Ω} [IsZeroOrProbabilityMeasure P]
    {s : Set Ω} {t : Set (Set Ω)} (hs : MeasurableSet s) (ht : ∀ i ∈ t, MeasurableSet i):
    IndepFrom s t P ↔ IndepSets {s} (generatePiSystem t) P := by
  rw [IndepFrom, ← generateFrom_generatePiSystem_eq (g := t)]
  constructor
  · intro h
    exact h.indepSets
  · intro h
    apply h.indep' _ _ (.singleton s) (isPiSystem_generatePiSystem _)
    · simpa
    · exact generatePiSystem_measurableSet ht

lemma IndepFrom.prob_inter_iInter [Countable ι] (h : IndepFrom s t P) {A : ι → Set Ω}
    (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t) : P (s ∩ ⋂ i, A i) = P s * P (⋂ i, A i) := by
  rw [IndepFrom, Indep_iff] at h
  rw [h]
  · exact .basic _ (by simp)
  apply MeasurableSet.iInter
  intro i
  obtain h | h := ht i
  · exact .basic _ h
  · exact .of_compl (.basic _ h)

lemma IndepFrom.prob_inter_biInter (h : IndepFrom s t P) {C : Set ι} {A : ι → Set Ω}
    (hC : C.Countable) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t) :
    P (s ∩ ⋂ i ∈ C, A i) = P s * P (⋂ i ∈ C, A i) := by
  have : Countable C := by simpa
  simpa using h.prob_inter_iInter (ι := C) (A := A ∘ Subtype.val) (by simpa)

lemma IndepFrom.prob_inter_sInter (h : IndepFrom s t P) (ht' : t'.Countable)
    (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) : P (s ∩ ⋂₀ t') = P s * P (⋂₀ t') := by
  rw [Set.sInter_eq_biInter]
  exact h.prob_inter_biInter ht' ht

variable [IsProbabilityMeasure P]

lemma IndepFrom.cond_iInter [Countable ι] (h : IndepFrom s t P)
    {A : ι → Set Ω} (hs : MeasurableSet s) (ht : ∀ i, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i, A i) ≠ 0) :
    P[s | ⋂ i, A i] = P s := by
  rw [cond_apply' hs, Set.inter_comm, h.prob_inter_iInter ht, mul_left_comm,
    ENNReal.inv_mul_cancel ht₀ (by simp), mul_one]

lemma IndepFrom.cond_biInter (h : IndepFrom s t P) {C : Set ι}
    {A : ι → Set Ω} (hC : C.Countable) (hs : MeasurableSet s) (ht : ∀ i ∈ C, A i ∈ t ∨ (A i)ᶜ ∈ t)
    (ht₀ : P (⋂ i ∈ C, A i) ≠ 0) :
    P[s | ⋂ i ∈ C, A i] = P s := by
  have : Countable C := by simpa
  simpa using h.cond_iInter (ι := C) (A := A ∘ Subtype.val) hs (by simpa) (by simpa)

lemma IndepFrom.cond_sInter (h : IndepFrom s t P) (hs : MeasurableSet s)
    (ht' : t'.Countable) (ht : ∀ i ∈ t', i ∈ t ∨ iᶜ ∈ t) (ht₀ : P (⋂₀ t') ≠ 0) :
    P[s | ⋂₀ t'] = P s := by
  rw [Set.sInter_eq_biInter] at ht₀ ⊢
  exact h.cond_biInter ht' hs ht (by simpa using ht₀)

end


variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}

def lopsidedCondition (P : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, ∀ S : Finset ι, i ∉ S → Disjoint (N i) S →
    P (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P (A i) * P (⋂ j ∈ S, (A j)ᶜ)

lemma lopsidedCondition.real [IsProbabilityMeasure P]
    (h : lopsidedCondition P A N) (hiS : i ∉ S) (hS : Disjoint (N i) S) :
    P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P.real (A i) * P.real (⋂ j ∈ S, (A j)ᶜ) := by
  rw [real_def, real_def, real_def, ← ENNReal.toReal_mul,
    ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  exact h _ _ hiS hS

def standardCondition (P : Measure Ω) (A : ι → Set Ω) (N : ι → Finset ι) : Prop :=
  ∀ i : ι, IndepFrom (A i) (A '' (insert i (N i))ᶜ) P

lemma lopsidedCondition_of_standardCondition [IsProbabilityMeasure P]
    (h : standardCondition P A N) :
    lopsidedCondition P A N := by
  intro i S hiS hS
  specialize h i
  simp only [← Finset.mem_coe (s := S)]
  rw [h.prob_inter_biInter (C := (S : Set ι)) (A := fun i ↦ (A i)ᶜ) S.countable_toSet _]
  intro j hj
  simp only [Finset.mem_coe] at hj
  right
  simp only [compl_compl]
  rw [Finset.disjoint_right] at hS
  apply Set.mem_image_of_mem
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Finset.mem_coe] -- TODO: try removing the simp
  grind

def IndividualBound (P : Measure Ω) (A : ι → Set Ω) (x : ι → ℝ) (i : ι) (S : Finset ι) : Prop :=
  P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ x i * P.real (⋂ j ∈ S, (A j)ᶜ)

lemma IndividualBound.compl [IsProbabilityMeasure P] (hA : MeasurableSet (A i))
    (h : IndividualBound P A x i S) :
    (1 - x i) * P.real (⋂ j ∈ S, (A j)ᶜ) ≤ P.real ((A i)ᶜ ∩ ⋂ j ∈ S, (A j)ᶜ) := by
  rw [IndividualBound] at h
  grw [one_sub_mul, ← h, ← Set.diff_eq_compl_inter, Set.inter_comm, sub_le_iff_le_add,
    ← measureReal_diff_add_inter hA]

open Finset

lemma iteration [DecidableEq ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {t t' : Finset ι} (ht : Disjoint t t')
    (hx₁ : ∀ i, x i ≤ 1)
    (S : Finset ι)
    (htS : t ⊆ S)
    (ht'S : t' ⊆ S)
    (h : ∀ T ⊂ S, ∀ {i}, i ∉ T → IndividualBound P A x i T) :
    (∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ) ≤ P.real (⋂ j ∈ t ∪ t', (A j)ᶜ) := by
  induction t using cons_induction_on with
  | empty => simp
  | cons a t hat ih =>
    replace ⟨hat', htt⟩ : a ∉ t' ∧ Disjoint t t' := by simpa using ht
    simp only [cons_eq_insert] at htS
    suffices ((1 - x a) * ∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ) ≤
        P.real ((A a)ᶜ ∩ (⋂ x ∈ t ∪ t', (A x)ᶜ)) by simpa [- mem_union, hat] using this
    calc
      _ = (1 - x a) * ((∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ)) := by ring
      _ ≤ (1 - x a) * P.real (⋂ j ∈ t ∪ t', (A j)ᶜ) := by
        gcongr
        · simp [hx₁]
        · apply ih htt ((subset_insert _ _).trans htS)
      _ ≤ _ := by
        have ha : a ∉ t ∪ t' := by simp [hat, hat']
        have : insert a (t ∪ t') ⊆ S := by
          simpa [insert_subset_iff, union_subset_iff, ht'S] using htS
        exact (h _ (Finset.ssubset_of_ssubset_of_subset (ssubset_insert ha) this) ha).compl (hA _)

lemma iteration_all [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {t : Finset ι}
    (hx₁ : ∀ i, x i ≤ 1)
    (h : ∀ i : ι, ∀ S : Finset ι, i ∉ S → IndividualBound P A x i S) :
    ∏ j ∈ t, (1 - x j) ≤ P.real (⋂ j ∈ t, (A j)ᶜ) := by
  have : ∀ T ⊂ t, ∀ {i}, i ∉ T → IndividualBound P A x i T := by
    intro T hTt i hiT
    exact h i T hiT
  classical
  simpa using iteration (P := P) hA (t' := ∅) (by simp) hx₁ t (by simp) (by simp) this

lemma prod_le_prod_of_subset_of_le_one {α : Type*} [CommMonoidWithZero α] [PartialOrder α]
    [PosMulMono α] [ZeroLEOneClass α]
    {x : ι → α} {s t : Finset ι} (hst : s ⊆ t)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i ≤ 1) :
    ∏ j ∈ t, x j ≤ ∏ j ∈ s, x j := by classical calc
  ∏ j ∈ t, x j = (∏ j ∈ t ∩ s, x j) * ∏ j ∈ t \ s, x j := by
    rw [prod_inter_mul_prod_diff]
  _ ≤ (∏ j ∈ t ∩ s, x j) * 1 := by
    gcongr
    · apply prod_nonneg
      simp [hx₀]
    · apply prod_le_one (by simp [hx₀]) (by simp [hx₁])
  _ = ∏ j ∈ s, x j := by simp [inter_eq_right.2 hst]

lemma individualBound [DecidableEq ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    (hN : lopsidedCondition P A N)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i ≤ 1)
    (hAx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j))
    (hiS : i ∉ S) :
    IndividualBound P A x i S := by
  induction S using strongInduction generalizing i with
  | H S ih =>
    let S₁ : Finset ι := S ∩ N i
    let S₂ : Finset ι := S \ S₁
    have hS : S₁ ∪ S₂ = S := by simp [S₁, S₂, union_comm (S ∩ N i), sdiff_union_inter]
    rw [IndividualBound]
    calc
      P.real (A i ∩ ⋂ j ∈ S, (A j)ᶜ) ≤ P.real (A i ∩ ⋂ j ∈ S₂, (A j)ᶜ) := by
        rw [← hS, Finset.set_biInter_inter]
        refine measureReal_mono ?_
        gcongr
        exact Set.inter_subset_right
      _ ≤ P.real (A i) * P.real (⋂ j ∈ S₂, (A j)ᶜ) :=
        hN.real (by simp [S₂, hiS]) (by simp [S₂, S₁, disjoint_sdiff])
      _ ≤ x i * (∏ j ∈ N i, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ) := by gcongr; exact hAx i
      _ = x i * ((∏ j ∈ N i, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ)) := by ring
      _ ≤ x i * ((∏ j ∈ S₁, (1 - x j)) * P.real (⋂ j ∈ S₂, (A j)ᶜ)) := by
        gcongr
        · exact hx₀ i
        apply prod_le_prod_of_subset_of_le_one (by simp [S₁]) (by simp [hx₁]) (by simp [hx₀])
      _ ≤ x i * P.real (⋂ j ∈ S, (A j)ᶜ) := by
        gcongr
        · exact hx₀ i
        rw [← hS]
        exact iteration hA disjoint_sdiff hx₁ _ (by simp [S₁]) (by simp [S₂]) ih

theorem localLemma [Fintype ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i ≤ 1)
    (h : lopsidedCondition P A N)
    (hAx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ P.real (⋂ i, (A i)ᶜ) := by
  have : ∀ i, ∀ S, i ∉ S → IndividualBound P A x i S := by
    intro i S hiS
    classical
    exact individualBound hA h hx₀ hx₁ hAx hiS
  simpa using iteration_all hA hx₁ this (t := univ)

lemma add_one_div_pow_le_exp {t : ℝ} {n : ℕ} (hn : n ≠ 0) (ht : 0 ≤ 1 + t / n) :
    (1 + t / n) ^ n ≤ Real.exp t := by
  grw [add_comm, Real.add_one_le_exp, ← Real.exp_nat_mul, mul_div_cancel₀ _ (by simpa)]
  rwa [add_comm]

lemma add_one_inv_pow_le_exp {n : ℕ} : (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 := by
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  simpa using add_one_div_pow_le_exp (t := 1) hn₀ (by positivity)

theorem symmetricLocalLemma [Fintype ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {d : ℕ} (hd : d ≠ 0) {p : ℝ} (h : lopsidedCondition P A N) (hAp : ∀ i, P.real (A i) ≤ p)
    (hN : ∀ i, #(N i) ≤ d)
    (hpd : Real.exp 1 * p * (d + 1) ≤ 1) :
    0 < P.real (⋂ i, (A i)ᶜ) := by
  let x (i : ι) : ℝ := (d + 1)⁻¹
  have hx₀ (i : ι) : 0 ≤ x i := by positivity
  have hx₁ (i : ι) : x i < 1 := inv_lt_one_of_one_lt₀ (by simp [hd, pos_iff_ne_zero])
  suffices hx : ∀ i, P.real (A i) ≤ x i * ∏ j ∈ N i, (1 - x j) from
    (localLemma hA hx₀ (fun i ↦ (hx₁ i).le) h hx).trans_lt' (prod_pos (by simp [hx₁]))
  intro i
  calc
    P.real (A i) ≤ p := hAp _
    _ ≤ (d + 1 : ℝ)⁻¹ * (Real.exp 1)⁻¹ := by
      rw [← mul_inv, ← one_div, le_div_iff₀]
      · linear_combination hpd
      · positivity
    _ ≤ (d + 1 : ℝ)⁻¹ * (1 + (↑d)⁻¹)⁻¹ ^ d := by
      grw [inv_pow, add_one_inv_pow_le_exp]
    _ = (d + 1 : ℝ)⁻¹ * (1 - (d + 1 : ℝ)⁻¹) ^ d := by
      congr! 2
      simp [field]
    _ ≤ (d + 1 : ℝ)⁻¹ * ∏ j ∈ N i, (1 - (d + 1 : ℝ)⁻¹) := by
      simp only [prod_const]
      gcongr _ * ?_
      apply pow_le_pow_of_le_one _ _ (by grind)
      · simpa using (hx₁ i).le
      · simpa [x] using hx₀ i
    _ = x i * ∏ j ∈ N i, (1 - x j) := rfl

-- lemma measurable_restrict_iff {ι β : Type*} [MeasurableSpace β] {s : Set ι} {T : Set (s → β)} :
--     MeasurableSet (s.restrict ⁻¹' T : Set (ι → β)) ↔ MeasurableSet T := by
--   refine ⟨?_, ?_⟩
--   -- obtain hβ | hβ := isEmpty_or_nonempty β
--   -- ·
--   intro hT
--   have : (s.restrict '' (s.restrict ⁻¹' T : Set (ι → β)) : Set (s → β)) = T := by
--     rw [Set.image_preimage_eq_inter_range]
--     sorry



-- #exit

lemma eq_sInter_of_mem_generatePiSystem {Ω : Type*} {t : Set (Set Ω)} {A : Set Ω}
    (hA : A ∈ generatePiSystem t) :
    ∃ S : Set (Set Ω), S ⊆ t ∧ A = ⋂₀ S := by
  induction hA with
  | @base s hs =>
    refine ⟨{s}, by simpa, by simp⟩
  | @inter s₁ s₂ _ _ h hs₁ hs₂ =>
    obtain ⟨S₁, hS₁, rfl⟩ := hs₁
    obtain ⟨S₂, hS₂, rfl⟩ := hs₂
    refine ⟨S₁ ∪ S₂, Set.union_subset hS₁ hS₂, by simp [Set.sInter_union]⟩

lemma standardCondition_of {α β : Type*} [MeasurableSpace β]
    [IsProbabilityMeasure P]
    {I : α → Ω → β} {A : ι → Set Ω} {N : ι → Finset ι}
    {D : ι → Finset α}
    (hND : ∀ i j, i ∉ N j → Disjoint (D i) (D j))
    (hI : ∀ a : α, Measurable (I a))
    (hI' : iIndepFun I P)
    (hA : ∀ i, ∃ S : Set (α → β), MeasurableSet S ∧
      DependsOn (· ∈ S) (D i) ∧ A i = {ω | (I · ω) ∈ S}) :
    standardCondition P A N := by
  rw [standardCondition]
  have hA' : ∀ i, MeasurableSet (A i) := by
    intro i
    obtain ⟨S, hS, -, h⟩ := hA i
    rw [h]
    apply MeasurableSet.preimage hS _
    rw [measurable_pi_iff]
    exact hI
  -- replace hA : ∀ i, ∃ S : Set (D i → β), A i = (fun ω ↦ (D i).restrict (I · ω)) ⁻¹' S := by
  --   intro i
  --   obtain ⟨S, hS, hD, h⟩ := hA i
  --   obtain ⟨S', rfl⟩ : ∃ S' : Set (D i → β), S = (D i).restrict ⁻¹' S' :=
  --     dependsOn_iff_exists_comp.1 hD
  --   exact ⟨S', h⟩
  intro i
  rw [IndepFrom]
  rw [← generateFrom_generatePiSystem_eq (g := _ '' _)]
  refine ProbabilityTheory.IndepSets.indep' ?_ ?_ (.singleton _)
    (isPiSystem_generatePiSystem _) ?_
  · simp only [Set.mem_singleton_iff, forall_eq]
    exact hA' i
  · apply generatePiSystem_measurableSet
    grind
  rw [ProbabilityTheory.IndepSets_iff]
  intro X₁ X₂ hX₁ hX₂
  cases hX₁
  replace hX₂ := eq_sInter_of_mem_generatePiSystem hX₂
  simp only [Set.exists_subset_image_iff, Set.sInter_image,
    Set.subset_compl_iff_disjoint_right, Set.disjoint_insert_right] at hX₂
  obtain ⟨J, hJ, rfl⟩ := hX₂
  classical
  -- J must be finite (subset of ι)
  by_cases hJ_fin : J.Finite
  swap; · exfalso; sorry -- J from finset operations
  lift J to Finset ι using hJ_fin
  -- For j ∈ J, we have j ∉ insert i (N i), so D j ⊥ D i
  have hDisj : ∀ j ∈ J, Disjoint (D j) (D i) := by
    intro j hj
    apply (hND j i _).symm
    intro h; cases h with
    | inl h => rw [h] at hj; exact hJ.1 (Set.mem_singleton _) (by simpa using hj)
    | inr h => exact hJ.2 (by simpa using hj) h
  -- Therefore D i ⊥ ⋃ j ∈ J, D j
  have hD_disj : Disjoint (D i : Set α) (J.biUnion D : Set α) := by
    rw [Finset.disjoint_biUnion_right]; exact fun j hj ↦ hDisj j hj
  -- From iIndepFun, restrictions to disjoint sets are independent
  have hIndep := hI'.indepFun_finset (D i) (J.biUnion D) (by simpa using hD_disj) (by fun_prop)
  -- Extract the measurable set representations
  obtain ⟨S_i, hS_i, hD_i, hAi⟩ := hA i
  obtain ⟨T_i, hT_eq⟩ := dependsOn_iff_exists_comp.1 hD_i
  -- The key step: express everything as preimages of restrictions
  -- and use hIndep.measure_inter_preimage_eq_mul
  sorry
