import Mathlib

open Finset

lemma Finset.card_le_one_iff_subsingleton {α : Type*} {S : Finset α} :
    #S ≤ 1 ↔ S.toSet.Subsingleton := by
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

def equipartitionToIco (a b k : ℕ) :
    Finpartition (Finset.Ico a b) :=
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



  -- simp only [Finpartition.parts, coe_image, coe_range, card_image, mem_range]
  -- exact Nat.card_range k

#exit

lemma exists_equipartition_Ico {a b k : ℕ} (hk : k ≠ 0) (hkn : k ≤ b - a) :
    ∃ P : Finpartition (Finset.Ico a b),
      P.IsEquipartition ∧ #P.parts = k ∧ ∀ i ∈ P.parts, ∃ c d, i = Finset.Ico c d := by
  set n := b - a
  set parts : Finset (Finset ℕ) := (Finset.range k).image fun i ↦
    Finset.Ico (a + equiEndpoint n k i) (a + equiEndpoint n k (i + 1))
  refine ⟨⟨parts, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [supIndep_iff_pairwiseDisjoint]
    simp_rw [parts, coe_image, coe_range]
    apply Set.Pairwise.image
    intro i hi j hj h
    simp only [Function.onFun, ← Finset.disjoint_coe, id_eq, coe_Ico]
    wlog hij : i ≤ j generalizing i j
    · exact (this hj hi h.symm (by order)).symm
    have : equiEndpoint n k (i + 1) ≤ equiEndpoint n k j := equiEndpoint_monotone (by omega)
    simp [this]



end Finpartition
