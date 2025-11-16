import Mathlib

open Finset

lemma Finset.card_le_one_iff_subsingleton {α : Type*} {S : Finset α} :
    #S ≤ 1 ↔ (S : Set α).Subsingleton := by
  rw [Finset.card_le_one_iff_subsingleton_coe, ← Set.subsingleton_coe]
  rfl

lemma Filter.Tendsto.exists_le_lt {α : Type*} [LinearOrder α] [NoMaxOrder α] {f : ℕ → α}
    (hf : Tendsto f atTop atTop) (n : α) (hn : f 0 ≤ n) : ∃ m, f m ≤ n ∧ n < f (m + 1) := by
  have h : ∃ m, n < f m := (hf.eventually (eventually_gt_atTop n)).exists
  match hm : Nat.find h with
  | 0 => cases hn.not_gt (hm ▸ Nat.find_spec h)
  | m + 1 => have : n < f m.succ := hm ▸ Nat.find_spec h
             refine ⟨m, le_of_not_gt <| Nat.find_min h <| m.lt_succ_self.trans_eq hm.symm, this⟩

lemma StrictMono.exists_le_lt {f : ℕ → ℕ} (hf : StrictMono f) (hf₀ : f 0 = 0) (n : ℕ) :
    ∃ m, f m ≤ n ∧ n < f (m + 1) :=
  hf.tendsto_atTop.exists_le_lt _ (by simp [hf₀])

lemma Fintype.piFinset_inter {ι α : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq α]
    {s t : ι → Finset α} :
    Fintype.piFinset s ∩ Fintype.piFinset t = Fintype.piFinset (fun i ↦ s i ∩ t i) := by
  ext j
  simp only [mem_inter, mem_piFinset]
  grind

lemma ENNReal.prod_div_distrib {ι : Type*} [DecidableEq ι] {f g : ι → ENNReal}
    (s : Finset ι) (h : ∀ i ∈ s, g i ≠ ⊤) :
    (∏ i ∈ s, f i / g i) = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    simp only [cons_eq_insert, mem_insert, ne_eq, forall_eq_or_imp] at h
    simp only [cons_eq_insert, has, not_false_eq_true, prod_insert]
    rw [ENNReal.mul_div_mul_comm (Or.inr (prod_ne_top h.2)) (Or.inl h.1), ih h.2]

lemma ENNReal.prod_div_distrib' {ι : Type*} [DecidableEq ι] {f g : ι → ENNReal}
    (s : Finset ι) (h : ∀ i ∈ s, g i ≠ 0) :
    (∏ i ∈ s, f i / g i) = (∏ i ∈ s, f i) / (∏ i ∈ s, g i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    simp only [cons_eq_insert, mem_insert, ne_eq, forall_eq_or_imp] at h
    simp only [cons_eq_insert, has, not_false_eq_true, prod_insert]
    rw [ENNReal.mul_div_mul_comm (Or.inl h.1)
      (Or.inr (by simpa [prod_eq_zero_iff] using h.2)), ih h.2]

section

open MeasureTheory Measure ProbabilityTheory

lemma uniformOn_apply_finset' {Ω : Type*} [DecidableEq Ω] [MeasurableSpace Ω] {s t : Finset Ω}
    (hs : MeasurableSet (s : Set Ω)) (ht : MeasurableSet (t : Set Ω)) :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s := by
  rw [uniformOn, cond_apply hs, count_apply_finset' hs, ← coe_inter, count_apply_finset']
  · rw [div_eq_mul_inv, mul_comm]
  rw [coe_inter]
  exact hs.inter ht

lemma uniformOn_apply_finset {Ω : Type*} [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {s t : Finset Ω} :
    uniformOn (s : Set Ω) (t : Set Ω) = #(s ∩ t) / #s :=
  uniformOn_apply_finset' s.measurableSet t.measurableSet

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}

lemma uniformOn_pi [Fintype Ω] [MeasurableSingletonClass Ω] {f : ι → Set Ω} :
    uniformOn (Set.univ.pi f) = Measure.pi fun i ↦ uniformOn (f i) := by
  refine (MeasureTheory.Measure.pi_eq fun t ht ↦ ?_).symm
  lift f to ι → Finset Ω
  · simp [Set.toFinite]
  lift t to ι → Finset Ω
  · simp [Set.toFinite]
  classical
  simp [← Fintype.coe_piFinset, uniformOn_apply_finset, Fintype.piFinset_inter,
    ENNReal.prod_div_distrib]

variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}

open Classical in
lemma map_pi_restrict (i₁ : Set ι)  :
    (Measure.pi P).map i₁.restrict = Measure.pi (fun i : i₁ ↦ P i) := by
  apply (Measure.pi_eq _).symm
  intro t hs
  rw [Measure.map_apply i₁.measurable_restrict (.pi Set.countable_univ (by simp [hs]))]
  have : (i₁.restrict ⁻¹' (Set.univ : Set i₁).pi t : Set (ι → Ω)) =
      Set.univ.pi fun i ↦ if h : i ∈ i₁ then t ⟨_, h⟩ else Set.univ := by grind
  calc
    Measure.pi P (i₁.restrict ⁻¹' Set.univ.pi t)
      = ∏ i, P i (if h : i ∈ i₁ then t ⟨i, h⟩ else Set.univ) := by rw [this, Measure.pi_pi]
    _ = ∏ i, if h : i ∈ i₁ then P i (t ⟨i, h⟩) else 1 := by simp [apply_dite (P _)]
    _ = _ := (Finset.prod_bij_ne_one (fun i _ _ ↦ i.1) (by simp) (by simp) (by simp) (by simp)).symm

lemma indepFun_restrict_restrict_pi {s t : Set ι} (hi : Disjoint s t) :
    IndepFun s.restrict t.restrict (Measure.pi P) := by
  lift s to Finset ι using s.toFinite
  lift t to Finset ι using t.toFinite
  simp only [disjoint_coe] at hi
  have : iIndepFun (fun x y ↦ y x) (Measure.pi P) := iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)
  have := this.indepFun_finset s t hi (by fun_prop)
  exact this

lemma pi_restrict_inter_restrict_eq {s t : Set ι} (hi : Disjoint s t)
    (A : Set (s → Ω)) (B : Set (t → Ω)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (s.restrict ⁻¹' A ∩ t.restrict ⁻¹' B) =
      Measure.pi P (s.restrict ⁻¹' A) * Measure.pi P (t.restrict ⁻¹' B) :=
  (indepFun_restrict_restrict_pi hi (P := P)).measure_inter_preimage_eq_mul A B hA hB

lemma MeasurableSet.of_restrict_preimage {ι β : Type*} [MeasurableSpace β]
    {s : Set ι} {T : Set (s → β)} (hT : (s.restrict ⁻¹' T : Set (ι → β)).Nonempty)
    (h : MeasurableSet (s.restrict ⁻¹' T : Set (ι → β))) :
    MeasurableSet T := by
  obtain ⟨x, -⟩ := hT
  classical
  let g (f : s → β) (y : ι) : β := if hy : y ∈ s then f ⟨y, hy⟩ else x y
  have hg : Measurable (fun f y ↦ if hy : y ∈ s then f ⟨y, hy⟩ else x y : (s → β) → _) :=
    measurable_pi_lambda _ (fun i ↦ by split <;> fun_prop)
  convert h.preimage hg
  ext i
  simp

lemma pi_inter_eq (s t : Set ι) (hst : Disjoint s t)
    (A B : Set (ι → Ω)) (hs : DependsOn (· ∈ A) s) (ht : DependsOn (· ∈ B) t)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (A ∩ B) = Measure.pi P A * Measure.pi P B := by
  obtain rfl | hAne := A.eq_empty_or_nonempty
  · simp
  obtain rfl | hBne := B.eq_empty_or_nonempty
  · simp
  obtain ⟨A', rfl⟩ : ∃ A', A = s.restrict ⁻¹' A' := dependsOn_iff_exists_comp.1 hs
  obtain ⟨B', rfl⟩ : ∃ B', B = t.restrict ⁻¹' B' := dependsOn_iff_exists_comp.1 ht
  rw [pi_restrict_inter_restrict_eq hst]
  · exact hA.of_restrict_preimage hAne
  · exact hB.of_restrict_preimage hBne

end



namespace Finpartition

def equiEndpoint (n k i : ℕ) : ℕ :=
  n / k * i + min (n % k) i

lemma equiEndpoint_lo {n k : ℕ} : equiEndpoint n k 0 = 0 := by
  simp [equiEndpoint]

lemma equiEndpoint_hi {n k : ℕ} (hk : k ≠ 0) : equiEndpoint n k k = n := by
  rw [equiEndpoint, min_eq_left (Nat.mod_lt n hk.bot_lt).le, Nat.div_add_mod']

lemma equiEndpoint_monotone {n k : ℕ} : Monotone (equiEndpoint n k) := by
  rintro i j h
  rw [equiEndpoint, equiEndpoint]
  gcongr

lemma equiEndpoint_strictMono {n k : ℕ} (hk : k ≠ 0) (hkn : k ≤ n) :
    StrictMono (equiEndpoint n k) := by
  rintro i j h
  rw [equiEndpoint, equiEndpoint]
  apply add_lt_add_of_lt_of_le
  · gcongr
    exact Nat.div_pos hkn hk.bot_lt
  · gcongr

open Function in
theorem equipartitionToIco.extracted_2 {n k a : ℕ} :
    Pairwise
      (Disjoint on (fun i ↦ Ico (a + equiEndpoint n k i) (a + equiEndpoint n k (i + 1)))) := by
  intro i j h
  simp only [Function.onFun, ← Finset.disjoint_coe, coe_Ico]
  wlog hij : i ≤ j generalizing i j
  · exact (this h.symm (by order)).symm
  have : equiEndpoint n k (i + 1) ≤ equiEndpoint n k j :=
    equiEndpoint_monotone (by omega)
  simp [this]

theorem equipartitionToIco.extracted_3 {a b k : ℕ} (hk₀ : k ≠ 0) (hk : k ≤ b - a) :
    ((range k).biUnion
      fun i ↦ Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))) =
      Ico a b := by
  apply subset_antisymm
  · simp only [biUnion_subset_iff_forall_subset, mem_range]
    intro i hi
    apply Ico_subset_Ico (by simp)
    calc
      _ ≤ a + equiEndpoint (b - a) k k := add_le_add_left (equiEndpoint_monotone (by omega)) a
      _ ≤ b := by rw [equiEndpoint_hi hk₀]; omega
  · simp only [subset_iff, mem_Ico, mem_biUnion, mem_range, and_imp]
    intro x hax hxb
    obtain ⟨i, hi, hi'⟩ :=
      (equiEndpoint_strictMono hk₀ hk).exists_le_lt (by rw [equiEndpoint_lo]) (x - a)
    have : i < k := by
      have : equiEndpoint (b - a) k k = b - a := equiEndpoint_hi hk₀
      by_contra!
      have : equiEndpoint (b - a) k k ≤ equiEndpoint (b - a) k i := equiEndpoint_monotone (by omega)
      omega
    exact ⟨i, this, by omega⟩

theorem equipartitionToIco_nonempty {a b k i : ℕ} (hk₀ : k ≠ 0) (hk : k ≤ b - a) :
    (Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))).Nonempty := by
  simp only [nonempty_Ico, add_lt_add_iff_left]
  exact equiEndpoint_strictMono hk₀ hk (Nat.lt_succ_self i)

def equipartitionToIco (a b k : ℕ) : Finpartition (Finset.Ico a b) :=
  if h : k ≠ 0 ∧ k ≤ b - a then {
    parts := (range k).image fun i ↦
      Finset.Ico (a + equiEndpoint (b - a) k i) (a + equiEndpoint (b - a) k (i + 1))
    supIndep := by
      rw [supIndep_iff_pairwiseDisjoint]
      simp_rw [coe_image, coe_range]
      apply Set.Pairwise.image
      intro i hi j hj h
      exact equipartitionToIco.extracted_2 h
    sup_parts := by
      rw [sup_eq_biUnion, image_biUnion]
      exact equipartitionToIco.extracted_3 h.1 h.2
    bot_notMem := by
      simp only [bot_eq_empty, mem_image, not_exists, not_and, ← nonempty_iff_ne_empty]
      intro i hi
      exact equipartitionToIco_nonempty h.1 h.2 }
  else ⊥

lemma card_equipartitionToIco_parts {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    #(equipartitionToIco a b k).parts = k := by
  rw [equipartitionToIco, dif_pos (by simp [hk, hkn]), card_image_of_injective, card_range]
  intro i j h
  by_contra! h'
  have h'' := equipartitionToIco.extracted_2 (a := a) (n := b - a) (k := k) h'
  dsimp at h
  simp only [Function.onFun, h, disjoint_self, bot_eq_empty] at h''
  have : (Ico (a + equiEndpoint (b - a) k j) (a + equiEndpoint (b - a) k (j + 1))).Nonempty :=
    equipartitionToIco_nonempty hk hkn
  simp [h''] at this

lemma card_of_mem_equipartitionToIco_parts_aux {n k i : ℕ} :
    equiEndpoint n k (i + 1) - equiEndpoint n k i = if i < n % k then n / k + 1 else n / k := by
  grind [equiEndpoint]

theorem card_of_mem_equipartitionToIco_parts
    {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a)
    (i : Finset ℕ) (hi : i ∈ (equipartitionToIco a b k).parts) :
    #i = (b - a) / k ∨ #i = (b - a) / k + 1 := by
  simp only [equipartitionToIco, ne_eq, hk, not_false_eq_true, hkn, and_self, ↓reduceDIte,
    mem_image, mem_range] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  simp only [Nat.card_Ico]
  have := card_of_mem_equipartitionToIco_parts_aux (n := b - a) (k := k) (i := i)
  grind

lemma isEquipartition_equipartitionToIco {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    (equipartitionToIco a b k).IsEquipartition := by
  rw [isEquipartition_iff_card_parts_eq_average]
  intro i hi
  simp only [Nat.card_Ico, card_equipartitionToIco_parts hk hkn]
  simp only [equipartitionToIco, ne_eq, hk, not_false_eq_true, hkn, and_self, ↓reduceDIte,
    mem_image, mem_range] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  simp only [Nat.card_Ico]
  have := card_of_mem_equipartitionToIco_parts_aux (n := b - a) (k := k) (i := i)
  grind

lemma exists_equipartition_Ico {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    ∃ P : Finpartition (Finset.Ico a b),
      P.IsEquipartition ∧ #P.parts = k ∧ ∀ i ∈ P.parts, ∃ c d, i = Finset.Ico c d := by
  refine ⟨equipartitionToIco _ _ k, isEquipartition_equipartitionToIco hk hkn,
    card_equipartitionToIco_parts hk hkn, ?_⟩
  intro i hi
  simp [equipartitionToIco, hk, hkn] at hi
  grind

end Finpartition
