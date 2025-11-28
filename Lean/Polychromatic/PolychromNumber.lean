import Polychromatic.Colouring

/-!
# The Polychromatic Number

This file defines and studies the polychromatic number of a finite set.

## Main definitions

* `polychromNumber S`: The polychromatic number of a finite set `S`, defined as the supremum
  of all `n` such that there exists a `Fin n`-valued `S`-polychromatic colouring.

## Main results

* `le_polychromNumber`: If `Fin n`-valued colouring exists, then `n ≤ polychromNumber S`.
* `polychromNumber_le_card`: The polychromatic number is at most `|S|`.
* `hasPolychromColouring_fin`: There exists an optimal colouring achieving the polychromatic number.
* `polychromNumber_vadd`: The polychromatic number is invariant under translation.
* `polychromNumber_neg`: The polychromatic number is invariant under negation.
* `polychromNumber_image`: The polychromatic number does not increase under group homomorphisms.
* `polychromNumber_iso`: The polychromatic number is preserved by group isomorphisms.
* `polychromNumber_subgroup`: The polychromatic number is preserved when embedding a subgroup.
* `polychromNumber_nsmul`: Scaling by a nonzero natural preserves the polychromatic number
  (in torsion-free groups).
* `polychromNumber_pair`: A pair has polychromatic number 2 (in torsion-free groups).
* `polychromNumber_three_eq_two`: The specific set `{0, 1, 3}` has polychromatic number 2.

## Implementation notes

The polychromatic number is defined as a supremum over natural numbers `n` such that
`HasPolychromColouring (Fin n) S`. This is well-defined because the set is bounded above by `|S|`.
-/

variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}

open Finset Fintype Pointwise

/-- The polychromatic number of a finite set `S`, defined as the supremum of all `n`
such that there exists a `Fin n`-valued `S`-polychromatic colouring. -/
-- ANCHOR: polychromNumber
noncomputable
def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}
-- ANCHOR_END: polychromNumber

/-- The polychromatic number is invariant under translation. -/
lemma polychromNumber_vadd [DecidableEq G] {n : G} :
    polychromNumber (n +ᵥ S) = polychromNumber S := by
  simp [polychromNumber]

private lemma bddAbove : BddAbove {n | HasPolychromColouring (Fin n) S} :=
  ⟨#S, fun n hn ↦ by simpa using hn.card_le⟩

private lemma nonempty (hS : S.Nonempty) : {n | HasPolychromColouring (Fin n) S}.Nonempty :=
  ⟨1, default, isPolychrom_subsingleton hS⟩

/-- If a `Fin n`-valued polychromatic colouring exists, then `n ≤ polychromNumber S`. -/
lemma le_polychromNumber {n : ℕ} (hn : HasPolychromColouring (Fin n) S) :
    n ≤ polychromNumber S :=
  le_csSup bddAbove hn

lemma card_le_polychromNumber [Fintype K] (hn : HasPolychromColouring K S) :
    card K ≤ polychromNumber S :=
  le_csSup bddAbove <| hn.of_surjective (equivFin K).surjective

@[simp] lemma polychromNumber_empty : polychromNumber (∅ : Finset G) = 0 := by
  simp [polychromNumber]

lemma one_le_polychromNumber (hS : S.Nonempty) : 1 ≤ polychromNumber S :=
  le_polychromNumber (hasPolychromColouring_subsingleton hS)

lemma polychromNumber_pos (hS : S.Nonempty) : 0 < polychromNumber S :=
  one_le_polychromNumber hS

/-- There exists an optimal colouring achieving the polychromatic number. -/
lemma hasPolychromColouring_fin (hS : S.Nonempty) :
    HasPolychromColouring (Fin (polychromNumber S)) S :=
  Nat.sSup_mem (nonempty hS) bddAbove

lemma hasPolychromColouring_of_card_le [Fintype K] [hK : Nonempty K]
    (hK : card K ≤ polychromNumber S) :
    HasPolychromColouring K S := by
  have hS : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simp at hK
  exact .of_injective (hasPolychromColouring_fin hS)
    (((equivFin K).toEmbedding.trans (Fin.castLEEmb hK)).injective)

lemma hasPolychromColouring_fin_of_le {n : ℕ}
    (hn : n ≠ 0) (hS : n ≤ polychromNumber S) :
    HasPolychromColouring (Fin n) S :=
  hasPolychromColouring_of_card_le (hK := Fin.pos_iff_nonempty.1 (by omega)) <| by simpa

/-- The polychromatic number is at most `|S|`. -/
-- ANCHOR: polychromNumber_le_card
lemma polychromNumber_le_card : polychromNumber S ≤ #S := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  simpa using (hasPolychromColouring_fin hS').card_le
-- ANCHOR_END: polychromNumber_le_card

lemma le_polychromNumber_iff_hasPolychromColouring {n : ℕ} (hn : n ≠ 0) {S : Finset G} :
    n ≤ polychromNumber S ↔ HasPolychromColouring (Fin n) S := by
  constructor
  · exact hasPolychromColouring_fin_of_le hn
  · exact le_polychromNumber

lemma polychromNumber_subset {S' : Finset G} (hS' : S' ⊆ S) :
    polychromNumber S' ≤ polychromNumber S := by
  obtain rfl | hS'' := S'.eq_empty_or_nonempty
  · simp
  exact le_polychromNumber ((hasPolychromColouring_fin hS'').subset hS')

@[simp] lemma polychromNumber_singleton {x : G} : polychromNumber {x} = 1 :=
  (polychromNumber_le_card.trans (by simp)).antisymm (one_le_polychromNumber (by simp))

lemma polychromNumber_eq_card_of_subsingleton (hS : (S : Set G).Subsingleton) :
    polychromNumber S = #S := by
  obtain rfl | ⟨x, hx⟩ := S.eq_empty_or_nonempty
  · simp
  rw [Set.subsingleton_iff_singleton (by simpa using hx)] at hS
  simp only [coe_eq_singleton] at hS
  simp [hS]

@[simp] lemma polychromNumber_univ [Fintype G] :
    polychromNumber (univ : Finset G) = Fintype.card G := by
  apply le_antisymm
  · exact polychromNumber_le_card
  · exact card_le_polychromNumber hasPolychromColouring_univ

/-- The polychromatic number does not increase under group homomorphisms. -/
-- Lemma 9
lemma polychromNumber_image {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F) {S : Finset G} :
    polychromNumber (S.image φ) ≤ polychromNumber S := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  exact le_polychromNumber (.of_image _ (hasPolychromColouring_fin (hS'.image φ)))

/-- The polychromatic number is preserved by group isomorphisms. -/
-- Corollary 10
lemma polychromNumber_iso {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [EquivLike F G H] [AddEquivClass F G H] (φ : F)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S :=
  le_antisymm (polychromNumber_image φ) <| by
    classical
    have : polychromNumber ((S.image φ).image (φ : G ≃ H).symm) ≤ polychromNumber (S.image φ) :=
      polychromNumber_image (φ : G ≃+ H).symm
    simpa [Finset.image_image] using this

/-- The polychromatic number is preserved when embedding a subgroup. -/
-- Lemma 11
lemma polychromNumber_subgroup [DecidableEq G] (H : AddSubgroup G) {S : Finset H} :
    polychromNumber S = polychromNumber (G := G) (S.image H.subtype) := by
  obtain rfl | hS' := S.eq_empty_or_nonempty
  · simp
  apply le_antisymm _ (polychromNumber_image H.subtype)
  obtain ⟨χ', hχ'⟩ := hasPolychromColouring_fin hS'
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
  suffices IsPolychrom (S.image H.subtype) χ from le_polychromNumber ⟨χ, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (h g) k
  refine ⟨i, by simpa, ?_⟩
  have : g = h g + v g := by simp [h]
  simp only [χ]
  rw [this, add_right_comm, ← AddSubgroup.coe_add, h_v, hi']

lemma polychromNumber_subgroup' (H : AddSubgroup G) {S : Finset G} (hSG : (S : Set G) ⊆ H) :
    polychromNumber (G := H) (S.preimage H.subtype (by simp)) = polychromNumber S := by
  classical
  rw [polychromNumber_subgroup H, Finset.image_preimage_of_bij]
  simpa +contextual [Set.BijOn, Set.SurjOn, Set.MapsTo, Set.subset_def] using hSG

lemma polychromNumber_image_injective {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] (φ : F) (hφ : Function.Injective φ)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S := by
  let ψ := AddMonoidHom.ofInjective (f := (φ : G →+ H)) hφ
  rw [← polychromNumber_iso ψ, polychromNumber_subgroup _, Finset.image_image]
  rfl

/-- Scaling by a nonzero natural preserves the polychromatic number (in torsion-free groups). -/
-- Lemma 12(i)
lemma polychromNumber_nsmul [DecidableEq G] [IsAddTorsionFree G] {k : ℕ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S :=
  polychromNumber_image_injective (nsmulAddMonoidHom k : G →+ G) (nsmul_right_injective hk)

lemma polychromNumber_zsmul [DecidableEq G] [IsAddTorsionFree G] {k : ℤ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S :=
  polychromNumber_image_injective (zsmulAddGroupHom k : G →+ G) (zsmul_right_injective hk)

private lemma polychromNumber_pair_aux_ℤ :
    polychromNumber ({0, 1} : Finset ℤ) = 2 := by
  set S : Finset ℤ := {0, 1}
  refine le_antisymm ?easy ?hard
  case easy =>
    have : #S = 2 := by simp [S]
    rw [← this]
    exact polychromNumber_le_card
  case hard =>
    suffices HasPolychromColouring (ZMod 2) S by
      simpa using card_le_polychromNumber this
    refine ⟨Int.castAddHom (ZMod 2), ?_⟩
    have : S.image (Int.castAddHom (ZMod 2)) = Finset.univ := rfl
    rw [isPolychrom_iff_mem_image]
    simp_rw [Finset.image_vadd_distrib, this]
    simp

private lemma polychromNumber_pair_aux [DecidableEq G] [IsAddTorsionFree G] {x : G} (hx : x ≠ 0) :
    polychromNumber {0, x} = 2 := by
  have : Function.Injective (zmultiplesHom G x) := by
    simpa [zmultiplesHom] using not_isOfFinAddOrder_of_isAddTorsionFree hx
  rw [← polychromNumber_pair_aux_ℤ, ← polychromNumber_image_injective _ this]
  simp

/-- A pair has polychromatic number 2 (in torsion-free groups). -/
@[simp] lemma polychromNumber_pair [DecidableEq G] [IsAddTorsionFree G] {x y : G} (hxy : x ≠ y) :
    polychromNumber {x, y} = 2 := by
  have := polychromNumber_pair_aux (x := y - x) (by simpa [sub_eq_zero, eq_comm] using hxy)
  rwa [← polychromNumber_vadd (n := x), Finset.vadd_finset_insert, Finset.vadd_finset_singleton,
    vadd_eq_add, add_zero, vadd_eq_add, add_sub_cancel] at this

lemma polychromNumber_eq_card_of_card_le_two [IsAddTorsionFree G] {S : Finset G} (hS : #S ≤ 2) :
    polychromNumber S = #S := by
  obtain hS2 | hS2 := lt_or_eq_of_le hS
  · rw [Nat.lt_succ_iff, Finset.card_le_one_iff_subsingleton] at hS2
    apply polychromNumber_eq_card_of_subsingleton hS2
  · classical
    rw [Finset.card_eq_two] at hS2
    obtain ⟨x, y, hxy, rfl⟩ := hS2
    simp [hxy]

lemma polychromNumber_le_of_forall {S : Finset G} {k : ℕ}
    (h : ∀ χ : G → Fin (k + 1), ¬ IsPolychrom S χ) :
    polychromNumber S ≤ k := by
  by_contra! h'
  obtain ⟨χ, hχ⟩ := hasPolychromColouring_fin_of_le (n := k + 1) (S := S) (by simp) (by cutsat)
  exact h _ hχ

section Int

lemma polychromNumber_mod_three_pair_eq_one : polychromNumber (G := ZMod 3) {0, 1} = 1 := by
  set S : Finset (ZMod 3) := {0, 1}
  refine le_antisymm ?hard ?easy
  case easy => exact one_le_polychromNumber (by simp [S])
  apply polychromNumber_le_of_forall
  decide

example : polychromNumber (G := ℤ) {0, 1, 5} = 3 := by
  set S : Finset ℤ := {0, 1, 5}
  refine le_antisymm ?easy ?hard
  case easy =>
    calc
      polychromNumber S ≤ #S := polychromNumber_le_card
      _ = 3 := by simp [S]
  case hard =>
    suffices HasPolychromColouring (ZMod 3) S by simpa using card_le_polychromNumber this
    refine ⟨Int.castAddHom (ZMod 3), ?_⟩
    have : S.image (Int.castAddHom (ZMod 3)) = Finset.univ := by decide
    rw [isPolychrom_iff_mem_image]
    simp_rw [Finset.image_vadd_distrib, this]
    simp

/-- The specific set `{0, 1, 3}` has polychromatic number 2. -/
-- ANCHOR: polychromNumber_three_eq_two
lemma polychromNumber_three_eq_two : polychromNumber (G := ℤ) {0, 1, 3} = 2 := by
-- ANCHOR_END: polychromNumber_three_eq_two
  set S : Finset ℤ := {0, 1, 3}
  refine le_antisymm ?hard ?easy
  case easy =>
    exact (polychromNumber_subset (S' := {0, 1}) (by simp [S])).trans' (by simp)
  case hard =>
    apply polychromNumber_le_of_forall
    intro χ hχ
    have h1 : ∃ i ∈ S, χ i = χ 2 := by simpa using hχ 0 (χ 2)
    have h2 : ∀ i ∈ S, ∃ n ∈ ({-1, 1, 2} : Finset ℤ), i ∈ n +ᵥ S ∧ 2 ∈ n +ᵥ S := by decide
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ¬ Set.InjOn χ (n +ᵥ S) := by
      obtain ⟨i, hi, hi2⟩ := h1
      obtain ⟨n, hn, hin, h2n⟩ := h2 i (by simpa)
      use n
      simp only [Set.InjOn, not_forall, exists_prop]
      exact ⟨i, hin, 2, h2n, hi2, by clear hin hi2; revert i; decide⟩
    simp_rw [isPolychrom_iff_surjOn, ← Finset.coe_univ] at hχ
    apply hn
    exact Finset.injOn_of_surjOn_of_card_le _ (by simp [Set.mapsTo_univ]) (hχ n) (by simp [S])

lemma polychromNumber_zmod_le {a b c : ℤ} {m : ℕ} (hm : m = c - a + b) :
    polychromNumber (({0, a, b, c} : Finset ℤ).image Int.cast : Finset (ZMod m)) =
      polychromNumber (({0, b - a, b, 2 * b - a} : Finset ℤ).image Int.cast : Finset (ZMod m)) := by
  set S₁ : Finset (ZMod m) := ({0, a, b, c} : Finset ℤ).image Int.cast
  set S₂ : Finset (ZMod m) := ({0, b - a, b, 2 * b - a} : Finset ℤ).image Int.cast
  have : S₂ = (Int.cast (b - a) : ZMod m) +ᵥ S₁ := by
    simp only [image_insert, Int.cast_zero, Int.cast_sub, image_singleton, Int.cast_mul,
      Int.cast_ofNat, vadd_finset_insert, vadd_eq_add, add_zero, sub_add_cancel,
      vadd_finset_singleton, S₂, S₁]
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
