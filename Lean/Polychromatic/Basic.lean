import Mathlib

variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Set G} {χ : G → K}

open Pointwise

def IsPolychrom (S : Set G) (χ : G → K) :
    Prop :=
  ∀ n : G, ∀ k, ∃ i ∈ n +ᵥ S, χ i = k
  -- ∀ n : G, Set.SurjOn χ (n +ᵥ S) Set.univ

lemma isPolychrom_iff :
    IsPolychrom S χ ↔ ∀ n : G, Set.SurjOn χ (n +ᵥ S) Set.univ := by
  simp [IsPolychrom, Set.SurjOn, Set.subset_def]

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
  have h1 : Set.SurjOn χ S Set.univ := by simpa using isPolychrom_iff.1 hχ 0
  exact .of_finite_univ (.of_surjOn _ h1 hS)

lemma IsPolychrom.natCard_le (hS : S.Finite) (hχ : IsPolychrom S χ) :
    Nat.card K ≤ Nat.card S :=
  have : Finite S := hS
  Nat.card_le_card_of_surjective _ <|
    Set.surjOn_iff_surjective.1 <|
    by simpa using isPolychrom_iff.1 hχ 0

lemma IsPolychrom.subset {S' : Set G} (hχ : IsPolychrom S' χ) (hS : S' ⊆ S) :
    IsPolychrom S χ :=
  isPolychrom_iff.2 fun n ↦ (isPolychrom_iff.1 hχ n).trans (by gcongr)

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
    HasPolychromColouring K₂ S := by
  obtain ⟨χ₁, hχ₁⟩ := h₁
  exact ⟨f ∘ χ₁, isPolychrom_iff.2 fun n ↦ (hf.surjOn _).comp (isPolychrom_iff.1 hχ₁ n)⟩

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

@[simp] lemma polychromNumber_pair {x y : G} (hxy : x ≠ y) : polychromNumber {x, y} = 2 :=
  sorry
