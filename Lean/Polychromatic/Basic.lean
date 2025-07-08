import Mathlib
import Polychromatic.ForMathlib.Misc

open Pointwise

section

variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Set G} {χ : G → K}

-- ANCHOR: IsPolychrom
def IsPolychrom (S : Set G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ i ∈ n +ᵥ S, χ i = k
-- ANCHOR_END: IsPolychrom

lemma isPolychrom_iff_surjOn :
    IsPolychrom S χ ↔ ∀ n : G, Set.SurjOn χ (n +ᵥ S) Set.univ := by
  simp [IsPolychrom, Set.SurjOn, Set.subset_def]

lemma isPolychrom_iff_mem : IsPolychrom S χ ↔ ∀ n : G, ∀ k, k ∈ χ '' (n +ᵥ S) :=
  Iff.rfl

lemma IsPolychrom.nonempty (h : IsPolychrom S χ) :
    S.Nonempty := by
  by_contra!
  simpa [this] using @h 0 (χ 0)

lemma isPolychrom_subsingleton [Subsingleton K] (hS : S.Nonempty) :
    IsPolychrom S χ := by
  intro n k
  obtain ⟨i, hi⟩ : (n +ᵥ S).Nonempty := by simpa
  exact ⟨_, hi, Subsingleton.elim _ _⟩

lemma IsPolychrom.finite (hS : S.Finite) (hχ : IsPolychrom S χ) :
    Finite K := by
  have h1 : Set.SurjOn χ S Set.univ := by simpa using isPolychrom_iff_surjOn.1 hχ 0
  exact .of_finite_univ (.of_surjOn _ h1 hS)

lemma IsPolychrom.natCard_le (hS : S.Finite) (hχ : IsPolychrom S χ) :
    Nat.card K ≤ Nat.card S :=
  have : Finite S := hS
  Nat.card_le_card_of_surjective _ <|
    Set.surjOn_iff_surjective.1 <|
    by simpa using isPolychrom_iff_surjOn.1 hχ 0

lemma IsPolychrom.subset {S' : Set G} (hχ : IsPolychrom S' χ) (hS : S' ⊆ S) :
    IsPolychrom S χ :=
  isPolychrom_iff_surjOn.2 fun n ↦ (isPolychrom_iff_surjOn.1 hχ n).trans (by gcongr)

lemma IsPolychrom.vadd (n : G) (h : IsPolychrom S χ) : IsPolychrom (n +ᵥ S) χ :=
  (vadd_vadd · n S ▸ h _)

@[simp] lemma isPolychrom_vadd {n : G} : IsPolychrom (n +ᵥ S) χ ↔ IsPolychrom S χ :=
  ⟨fun h ↦ by simpa using h.vadd (-n), fun h ↦ h.vadd n⟩

def HasPolychromColouring (K : Type*) (S : Set G) :
    Prop :=
  ∃ χ : G → K, IsPolychrom S χ

lemma HasPolychromColouring.nonempty (h : HasPolychromColouring K S) : S.Nonempty := by
  obtain ⟨χ, hχ⟩ := h
  exact hχ.nonempty

lemma HasPolychromColouring.nonempty' (h : HasPolychromColouring K S) : Nonempty K := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨χ 0⟩

@[simp] lemma not_hasPolychromColouring_empty : ¬ HasPolychromColouring K (∅ : Set G) := by
  intro h
  simpa using h.nonempty

lemma hasPolychromColouring_subsingleton [Nonempty K] [Subsingleton K] (hS : S.Nonempty) :
    HasPolychromColouring K S := by
  inhabit K
  exact ⟨fun _ ↦ default, isPolychrom_subsingleton hS⟩

lemma HasPolychromColouring.natCard_le (hS : S.Finite) (h : HasPolychromColouring K S) :
    Nat.card K ≤ Nat.card S :=
  have ⟨_, hχ⟩ := h; hχ.natCard_le hS

lemma HasPolychromColouring.finite (hS : S.Finite) (h : HasPolychromColouring K S) :
    Finite K :=
  have ⟨_, hχ⟩ := h; hχ.finite hS

lemma HasPolychromColouring.subset {S' : Set G} (h : HasPolychromColouring K S') (hS : S' ⊆ S) :
    HasPolychromColouring K S :=
  have ⟨χ, hχ⟩ := h; ⟨χ, hχ.subset hS⟩

lemma HasPolychromColouring.of_surjective {K₁ K₂ : Type*}
    (h₁ : HasPolychromColouring K₁ S) {f : K₁ → K₂} (hf : f.Surjective) :
    HasPolychromColouring K₂ S :=
  have ⟨χ₁, hχ₁⟩ := h₁
  ⟨f ∘ χ₁, isPolychrom_iff_surjOn.2 fun n ↦ (hf.surjOn _).comp (isPolychrom_iff_surjOn.1 hχ₁ n)⟩

@[simp] lemma hasPolychromColouring_vadd {n : G} :
    HasPolychromColouring K (n +ᵥ S) ↔ HasPolychromColouring K S := by
  simp [HasPolychromColouring]

alias ⟨_, HasPolychromColouring.vadd⟩ := hasPolychromColouring_vadd

noncomputable def polychromNumber (S : Set G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}

lemma polychromNumber_vadd {n : G} : polychromNumber (n +ᵥ S) = polychromNumber S := by
  simp [polychromNumber]

private lemma bddAbove (hS : S.Finite) : BddAbove {n | HasPolychromColouring (Fin n) S} :=
  ⟨Nat.card S, fun n hn ↦ Nat.card_fin n ▸ hn.natCard_le hS⟩

private lemma nonempty (hS : S.Nonempty) : {n | HasPolychromColouring (Fin n) S}.Nonempty :=
  ⟨1, default, isPolychrom_subsingleton hS⟩

lemma le_polychromNumber (hS : S.Finite) {n : ℕ} (hn : HasPolychromColouring (Fin n) S) :
    n ≤ polychromNumber S :=
  le_csSup (bddAbove hS) hn

lemma natCard_le_polychromNumber (hS : S.Finite) (hn : HasPolychromColouring K S) :
    Nat.card K ≤ polychromNumber S :=
  le_csSup (bddAbove hS) <|
    have : Finite K := hn.finite hS
    hn.of_surjective (Finite.equivFin K).surjective

@[simp] lemma polychromNumber_empty : polychromNumber (∅ : Set G) = 0 := by simp [polychromNumber]

lemma one_le_polychromNumber (hS : S.Finite) (hS' : S.Nonempty) :
    1 ≤ polychromNumber S := by
  have : HasPolychromColouring (Fin 1) S := hasPolychromColouring_subsingleton hS'
  exact le_polychromNumber hS this

lemma polychromNumber_pos (hS : S.Finite) (hS' : S.Nonempty) :
    0 < polychromNumber S :=
  one_le_polychromNumber hS hS'

lemma hasPolychromColouring_fin (hS : S.Finite) (hS' : S.Nonempty) :
    HasPolychromColouring (Fin (polychromNumber S)) S :=
  Nat.sSup_mem (nonempty hS') (bddAbove hS)

lemma hasPolychromColouring_of_natCard_le [Finite K] [hK : Nonempty K] (hS : S.Finite)
    (hK : Nat.card K ≤ polychromNumber S) :
    HasPolychromColouring K S := by
  have hS' : S.Nonempty := by
    by_contra!
    subst this
    simp only [polychromNumber_empty] at hK
    exact (Nat.card_pos (α := K)).not_ge hK
  obtain ⟨f, hf⟩ : ∃ f : Fin (polychromNumber S) → K, Function.Surjective f := by
    have : Cardinal.mk K ≤ polychromNumber S := by simpa [← Nat.cast_card]
    rw [Function.exists_surjective_iff, ← Cardinal.lift_mk_le']
    simp [← Fin.pos_iff_nonempty, polychromNumber_pos hS hS', *]
  exact .of_surjective (hasPolychromColouring_fin hS hS') hf

lemma hasPolychromColouring_fin_of_le (hS : S.Finite) {n : ℕ}
    (hn : n ≠ 0) (hK : n ≤ polychromNumber S) :
    HasPolychromColouring (Fin n) S :=
  hasPolychromColouring_of_natCard_le (hK := Fin.pos_iff_nonempty.1 (by omega)) hS <| by simpa

lemma polychromNumber_le_card (hS : S.Finite) :
    polychromNumber S ≤ Nat.card S := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  simpa using (hasPolychromColouring_fin hS hS').natCard_le hS

lemma polychromNumber_subset (hS : S.Finite) {S' : Set G} (hS' : S' ⊆ S) :
    polychromNumber S' ≤ polychromNumber S := by
  obtain rfl | hS'' := S'.eq_empty_or_nonempty
  · simp
  exact le_polychromNumber hS ((hasPolychromColouring_fin (hS.subset hS') hS'').subset hS')

@[simp] lemma polychromNumber_singleton {x : G} : polychromNumber {x} = 1 :=
  ((polychromNumber_le_card (by simp)).trans (by simp)).antisymm
    (one_le_polychromNumber (by simp) (by simp))

lemma polychromNumber_eq_natCard_of_subsingleton {S : Set G} (hS : S.Subsingleton) :
    polychromNumber S = Nat.card S := by
  obtain rfl | ⟨x, hx⟩ := S.eq_empty_or_nonempty
  · simp
  rw [Set.subsingleton_iff_singleton hx] at hS
  simp [hS]

-- Lemma 9
lemma polychromNumber_image {H : Type*} [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F)
    {S : Set G} (hS : S.Finite) :
    polychromNumber (φ '' S) ≤ polychromNumber S := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  obtain ⟨χ', hχ'⟩ := hasPolychromColouring_fin (hS.image φ) (hS'.image _)
  let χ (g : G) : Fin (polychromNumber (φ '' S)) := χ' (φ g)
  suffices IsPolychrom S χ from le_polychromNumber hS ⟨_, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (φ g) k
  rw [← Set.image_vadd_distrib] at hi
  aesop

-- Corollary 10
lemma polychromNumber_iso {H : Type*} [AddCommGroup H]
    {F : Type*} [EquivLike F G H] [AddEquivClass F G H] (φ : F)
    {S : Set G} (hS : S.Finite) :
    polychromNumber (φ '' S) = polychromNumber S :=
  le_antisymm (polychromNumber_image φ hS) <| by
    have : polychromNumber ((φ : G ≃+ H).symm '' (φ '' S)) ≤ polychromNumber (φ '' S) :=
      polychromNumber_image _ (hS.image _)
    simpa [Set.image_image] using this

-- Lemma 11
lemma polychromNumber_subgroup (H : AddSubgroup G) {S : Set H} (hS : S.Finite) :
    polychromNumber S = polychromNumber (G := G) (H.subtype '' S) := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  apply le_antisymm _ (polychromNumber_image H.subtype hS)
  obtain ⟨χ', hχ'⟩ := hasPolychromColouring_fin hS hS'
  let v (g : G) : G := Quotient.out (QuotientAddGroup.mk g : G ⧸ H) - Quotient.out (0 : G ⧸ H)
  have hv (g : G) : g - v g ∈ H := by
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk_out_eq_mul H g
    obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_mul H 0
    simp only [QuotientAddGroup.mk_zero, zero_add] at hb
    have : g - (g + a - b) = (b - a : H) := by simp; abel
    simp only [v, ha, hb, this]
    exact SetLike.coe_mem (b - a)
  let h (g : G) : H := ⟨g - v g, hv g⟩
  have h_idem (i : H) : h i = i := by
    ext1
    simp only [sub_eq_self, v, h, sub_eq_zero, Quotient.out_inj, ← QuotientAddGroup.mk_zero]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simp
  have h_v (i : H) (g : G) : h (i + v g) = i := by
    have : v (i + v g) = v g := by
      rw [sub_left_inj, Quotient.out_inj, eq_comm, QuotientAddGroup.eq_iff_sub_mem,
        sub_add_eq_sub_sub_swap]
      exact H.sub_mem (hv _) (SetLike.coe_mem i)
    simp [h, this]
  let χ : G → Fin (polychromNumber S) := fun g ↦ χ' (h g)
  suffices IsPolychrom (H.subtype '' S) χ from le_polychromNumber (hS.image _) ⟨χ, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (h g) k
  rw [Set.mem_vadd_set] at hi
  obtain ⟨t, ht, ht'⟩ := hi
  have : g = h g + v g := by simp [h]
  refine ⟨g + t, Set.vadd_mem_vadd_set ⟨_, ht, rfl⟩, ?_⟩
  simp only [χ]
  rw [this, add_right_comm, ← AddSubgroup.coe_add, h_v, ← vadd_eq_add, ht', hi']

lemma polychromNumber_subgroup' (H : AddSubgroup G) {S : Set G} (hS : S.Finite) (hSG : S ⊆ H) :
    polychromNumber (G := H) (H.subtype ⁻¹' S) = polychromNumber S := by
  have : (H.subtype ⁻¹' S).Finite := hS.preimage H.subtype_injective.injOn
  rw [polychromNumber_subgroup H this, Set.image_preimage_eq_of_subset]
  simpa

lemma polychromNumber_image_injective {H : Type*} [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] (φ : F) (hφ : Function.Injective φ)
    {S : Set G} (hS : S.Finite) :
    polychromNumber (φ '' S) = polychromNumber S := by
  let ψ := AddMonoidHom.ofInjective (f := (φ : G →+ H)) hφ
  rw [← polychromNumber_iso ψ hS, polychromNumber_subgroup _ (hS.image _), Set.image_image]
  rfl

-- Lemma 12(i)
lemma polychromNumber_smul [IsAddTorsionFree G] {k : ℕ} (hk : k ≠ 0) (hS : S.Finite) :
    polychromNumber ((k • ·) '' S) = polychromNumber S := by
  rw [← polychromNumber_image_injective (nsmulAddMonoidHom k) (nsmul_right_injective hk) hS]
  simp

private lemma polychromNumber_pair_aux_ℤ :
    polychromNumber {0, (1 : ℤ)} = 2 := by
  set S : Set ℤ := {0, 1}
  refine le_antisymm ?easy ?hard
  case easy =>
    have : Nat.card S = 2 := by simp
    rw [← this]
    exact polychromNumber_le_card (by simp [S])
  case hard =>
    suffices HasPolychromColouring (ZMod 2) S by
      simpa using natCard_le_polychromNumber (by simp [S]) this
    refine ⟨Int.castAddHom (ZMod 2), ?_⟩
    have : Int.castAddHom (ZMod 2) '' S = Set.univ := Set.toFinset_eq_univ.mp rfl
    rw [isPolychrom_iff_mem]
    simp_rw [Set.image_vadd_distrib, this]
    simp

private lemma polychromNumber_pair_aux [IsAddTorsionFree G] {x : G} (hx : x ≠ 0) :
    polychromNumber {0, x} = 2 := by
  have : Function.Injective (zmultiplesHom G x) := by
    simpa [zmultiplesHom] using not_isOfFinAddOrder_of_isAddTorsionFree hx
  rw [← polychromNumber_pair_aux_ℤ, ← polychromNumber_image_injective _ this (by simp)]
  simp [Set.image_pair]

@[simp] lemma polychromNumber_pair [IsAddTorsionFree G] {x y : G} (hxy : x ≠ y) :
    polychromNumber {x, y} = 2 := by
  have := polychromNumber_pair_aux (x := y - x) (by simpa [sub_eq_zero, eq_comm] using hxy)
  rwa [← polychromNumber_vadd (n := x), Set.vadd_set_insert, Set.vadd_set_singleton, vadd_eq_add,
    add_zero, vadd_eq_add, add_sub_cancel] at this

lemma polychromNumber_eq_natCard_of_natCard_le_two [IsAddTorsionFree G] {S : Set G}
    (hS' : S.Finite)
    (hS : Nat.card S ≤ 2) :
    polychromNumber S = Nat.card S := by
  lift S to Finset G using hS'
  rw [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe] at hS
  obtain hS2 | hS2 := lt_or_eq_of_le hS
  · rw [Nat.lt_succ_iff, Finset.card_le_one_iff_subsingleton] at hS2
    apply polychromNumber_eq_natCard_of_subsingleton hS2
  · classical
    rw [Finset.card_eq_two] at hS2
    obtain ⟨x, y, hxy, rfl⟩ := hS2
    simp [hxy]

end

section Int

example : polychromNumber ({0, 1, 5} : Set ℤ) = 3 := by
  set S : Set ℤ := {0, 1, 5}
  refine le_antisymm ?easy ?hard
  case easy =>
    calc
      polychromNumber S ≤ Nat.card S := polychromNumber_le_card (by simp [S])
      _ = 3 := by simp [S]
  case hard =>
    suffices HasPolychromColouring (ZMod 3) S by
      simpa using natCard_le_polychromNumber (by simp [S]) this
    refine ⟨Int.castAddHom (ZMod 3), ?_⟩
    have : Int.castAddHom (ZMod 3) '' S = Set.univ := by
      rw [← Set.toFinset_eq_univ]
      decide
    rw [isPolychrom_iff_mem]
    simp_rw [Set.image_vadd_distrib, this]
    simp

example : polychromNumber ({0, 1, 3} : Set ℤ) = 2 := by
  set S : Set ℤ := {0, 1, 3}
  set S' : Finset ℤ := {0, 1, 3}
  have hS' : S' = S := by simp [S, S']
  rw [← hS'] at *
  have : polychromNumber S'.toSet < 3 := by
    by_contra!
    obtain ⟨χ, hχ⟩ := hasPolychromColouring_fin_of_le (by simp [S']) (by simp) this
    have h1 : ∃ i ∈ S', χ i = χ 2 := by simpa using hχ 0 (χ 2)
    have h2 : ∀ i ∈ S', ∃ n ∈ ({-1, 1, 2} : Finset ℤ), i ∈ n +ᵥ S' ∧ 2 ∈ n +ᵥ S' := by
      decide
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ¬ Set.InjOn χ (n +ᵥ S') := by
      obtain ⟨i, hi, hi2⟩ := h1
      obtain ⟨n, hn, hin, h2n⟩ := h2 i (by simpa [← Finset.mem_coe, hS'])
      use n
      simp only [Set.InjOn, not_forall, exists_prop]
      exact ⟨i, hin, 2, h2n, hi2, by fin_cases hi <;> decide⟩
    simp_rw [isPolychrom_iff_surjOn, ← Finset.coe_vadd_finset, ← Finset.coe_univ] at hχ
    apply hn
    exact Finset.injOn_of_surjOn_of_card_le _ (by simp [Set.mapsTo_univ]) (hχ n) (by simp [S'])
  have : 2 ≤ polychromNumber S'.toSet := by
    refine (polychromNumber_subset (S' := {0, 1}) (by simp) (by simp [S'])).trans' ?_
    simp [polychromNumber_pair]
  omega

lemma polychromNumber_zmod_le {a b c : ℤ} {m : ℕ} (hm : m = c - a + b) :
    polychromNumber (Int.cast '' {0, a, b, c} : Set (ZMod m)) =
      polychromNumber (Int.cast '' {0, b - a, b, 2 * b - a} : Set (ZMod m)) := by
  set S₁ : Set (ZMod m) := Int.cast '' {0, a, b, c}
  set S₂ : Set (ZMod m) := Int.cast '' {0, b - a, b, 2 * b - a}
  have : S₂ = (Int.cast (b - a) : ZMod m) +ᵥ S₁ := by
    simp only [S₁, S₂, Set.image_singleton, Set.image_insert_eq, Set.vadd_set_insert, Int.cast_sub,
      Set.vadd_set_singleton, vadd_eq_add, Int.cast_mul, Int.cast_ofNat, sub_add_cancel,
      Int.cast_zero, add_zero]
    have : (b : ZMod m) - a + c = 0 := by
      calc
        (b : ZMod m) - a + c = c - a + b := by ring
        _ = ↑(c - a + b : ℤ) := by simp
        _ = (m : ℤ) := by rw [hm]
        _ = 0 := by simp
    rw [this, sub_add_eq_add_sub, ← two_mul]
    ext i
    simp
    tauto
  rw [this, polychromNumber_vadd]

end Int
