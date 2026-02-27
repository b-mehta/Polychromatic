import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Polychromatic.ForMathlib.Misc

/-!
# Polychromatic Colourings - Core Definitions

This file defines the core notions of polychromatic colourings.

## Main definitions

* `IsPolychrom S χ`: A predicate stating that the colouring `χ` is `S`-polychromatic,
  meaning that every translate of the finite set `S` contains an element of each colour.

* `HasPolychromColouring K S`: A predicate stating that there exists a `K`-valued colouring
  that is `S`-polychromatic.

## Main results

* `IsPolychrom.card_le`: The number of colours is at most the size of the set `S`.
* `HasPolychromColouring.subset`: If a smaller set has a polychromatic colouring,
  so does any superset.
* `HasPolychromColouring.of_surjective`: Polychromatic colourings transfer along surjections.
* `hasPolychromColouring_vadd`: The existence of a polychromatic colouring is
  invariant under translation.

## Implementation notes

The definition `IsPolychrom` uses an additive formulation where `χ (n + a) = k` for some `a ∈ S`,
which is equivalent to saying that every translate `n + S` hits every colour class.
-/

open Pointwise

section

variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}

open Finset

/-- A colouring `χ : G → K` is `S`-polychromatic if every translate of `S` contains an element
of each colour class. Equivalently, for every `n : G` and every colour `k : K`, there exists
some `a ∈ S` such that `χ(n + a) = k`. -/
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k

/-- If `χ` is `S`-polychromatic then `S` must be nonempty. -/
-- ANCHOR IsPolychrom.nonempty
lemma IsPolychrom.nonempty (h : IsPolychrom S χ) :
    S.Nonempty := by
  obtain ⟨i, hi, hi'⟩ := h 0 (χ 0)
  use i
-- ANCHOR_END IsPolychrom.nonempty

lemma isPolychrom_subsingleton [Subsingleton K] (hS : S.Nonempty) :
    IsPolychrom S χ := by
  intro n k
  obtain ⟨i, hi⟩ := hS
  exact ⟨_, hi, Subsingleton.elim _ _⟩

section decEq

variable [DecidableEq G]

lemma isPolychrom_iff :
    IsPolychrom S χ ↔ ∀ n : G, ∀ k : K, ∃ i ∈ n +ᵥ S, χ i = k := by
  simp [IsPolychrom, Finset.mem_vadd_finset]

set_option linter.unusedSimpArgs false in
lemma isPolychrom_iff_surjOn :
    IsPolychrom S χ ↔ ∀ n : G, Set.SurjOn χ (n +ᵥ S) Set.univ := by
  simp [isPolychrom_iff, Set.SurjOn, Set.subset_def, ← Finset.coe_vadd_finset]

alias ⟨IsPolychrom.surjOn, _⟩ := isPolychrom_iff_surjOn

lemma isPolychrom_iff_mem_image [DecidableEq K] :
    IsPolychrom S χ ↔ ∀ n : G, ∀ k, k ∈ (n +ᵥ S).image χ := by
  simp [isPolychrom_iff]

alias ⟨IsPolychrom.mem_image, _⟩ := isPolychrom_iff_mem_image

end decEq

def IsPolychrom.fintype [DecidableEq K] (hχ : IsPolychrom S χ) :
    Fintype K where
  elems := S.image χ
  complete := by classical simpa using hχ.mem_image 0

lemma IsPolychrom.finite (hχ : IsPolychrom S χ) :
    Finite K := by
  classical exact hχ.fintype.finite

/-- The number of colours in any `S`-polychromatic colouring is at most `|S|`. -/
lemma IsPolychrom.card_le [Fintype K] (hχ : IsPolychrom S χ) :
    Fintype.card K ≤ #S :=
  card_le_card_of_surjOn χ (by classical simpa using hχ.surjOn 0)

lemma IsPolychrom.subset {S' : Finset G} (hχ : IsPolychrom S' χ) (hS : S' ⊆ S) :
    IsPolychrom S χ := by
  classical exact isPolychrom_iff_surjOn.2 fun n ↦ (hχ.surjOn n).trans (by gcongr)

lemma IsPolychrom.vadd [DecidableEq G] (n : G) (h : IsPolychrom S χ) : IsPolychrom (n +ᵥ S) χ := by
  rw [isPolychrom_iff] at h ⊢
  simp_rw [vadd_vadd]
  intro n
  exact h _

@[simp] lemma isPolychrom_vadd [DecidableEq G] {n : G} : IsPolychrom (n +ᵥ S) χ ↔ IsPolychrom S χ :=
  ⟨fun h ↦ by simpa using h.vadd (-n), fun h ↦ h.vadd n⟩

lemma IsPolychrom.neg [DecidableEq G] (h : IsPolychrom S χ) :
    IsPolychrom (-S) (fun g ↦ χ (-g)) := by
  intro n g
  obtain ⟨a, ha, hg⟩ := h (-n) g
  refine ⟨-a, by simpa, ?_⟩
  simpa only [neg_add, neg_neg]

lemma isPolychrom_univ_id [Fintype G] :
    IsPolychrom univ (id : G → G) := by
  classical simp [isPolychrom_iff]

instance [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K] : Decidable (IsPolychrom S χ) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- There exists a `K`-valued `S`-polychromatic colouring of `G`. -/
def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ

lemma HasPolychromColouring.nonempty_set (h : HasPolychromColouring K S) : S.Nonempty := by
  obtain ⟨χ, hχ⟩ := h
  exact hχ.nonempty

lemma HasPolychromColouring.nonempty_colours (h : HasPolychromColouring K S) : Nonempty K := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨χ 0⟩

@[simp] lemma not_hasPolychromColouring_empty : ¬ HasPolychromColouring K (∅ : Finset G) := by
  intro h
  simpa using h.nonempty_set

lemma hasPolychromColouring_subsingleton [Nonempty K] [Subsingleton K] (hS : S.Nonempty) :
    HasPolychromColouring K S := by
  inhabit K
  exact ⟨fun _ ↦ default, isPolychrom_subsingleton hS⟩

lemma HasPolychromColouring.card_le [Fintype K] (h : HasPolychromColouring K S) :
    Fintype.card K ≤ #S :=
  have ⟨_, hχ⟩ := h; hχ.card_le

lemma HasPolychromColouring.finite (h : HasPolychromColouring K S) :
    Finite K :=
  have ⟨_, hχ⟩ := h; hχ.finite

/-- If `S'` has a `K`-polychromatic colouring and `S' ⊆ S`, then `S` also has one. -/
lemma HasPolychromColouring.subset {S' : Finset G} (h : HasPolychromColouring K S') (hS : S' ⊆ S) :
    HasPolychromColouring K S :=
  have ⟨χ, hχ⟩ := h; ⟨χ, hχ.subset hS⟩

/-- If `S` has a `K₁`-polychromatic colouring and `f : K₁ → K₂` is surjective,
then `S` has a `K₂`-polychromatic colouring. -/
lemma HasPolychromColouring.of_surjective {K₁ K₂ : Type*}
    (h₁ : HasPolychromColouring K₁ S) {f : K₁ → K₂} (hf : f.Surjective) :
    HasPolychromColouring K₂ S :=
  have ⟨χ₁, hχ₁⟩ := h₁
  ⟨f ∘ χ₁, by classical exact isPolychrom_iff_surjOn.2 fun n ↦ hf.surjOn.comp (hχ₁.surjOn n)⟩

lemma HasPolychromColouring.of_injective {K₁ K₂ : Type*} [Nonempty K₁]
    (h₁ : HasPolychromColouring K₂ S) {f : K₁ → K₂} (hf : f.Injective) :
    HasPolychromColouring K₁ S :=
  h₁.of_surjective (Function.invFun_surjective hf)

/-- The existence of a polychromatic colouring is invariant under translation:
`n +ᵥ S` has a `K`-polychromatic colouring iff `S` does. -/
@[simp] lemma hasPolychromColouring_vadd [DecidableEq G] {n : G} :
    HasPolychromColouring K (n +ᵥ S) ↔ HasPolychromColouring K S := by
  simp [HasPolychromColouring]

alias ⟨_, HasPolychromColouring.vadd⟩ := hasPolychromColouring_vadd

lemma HasPolychromColouring.neg [DecidableEq G] (h : HasPolychromColouring K S) :
    HasPolychromColouring K (-S) := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨fun g ↦ χ (-g), hχ.neg⟩

@[simp] lemma hasPolychromColouring_neg [DecidableEq G] :
    HasPolychromColouring K (-S) ↔ HasPolychromColouring K S :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩

@[simp] lemma hasPolychromColouring_univ [Fintype G] :
    HasPolychromColouring G (Finset.univ : Finset G) :=
  ⟨id, isPolychrom_univ_id⟩

lemma HasPolychromColouring.of_image {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F)
    (h : HasPolychromColouring K (S.image φ)) :
    HasPolychromColouring K S := by
  obtain ⟨χ', hχ'⟩ := h
  let χ (g : G) : K := χ' (φ g)
  suffices IsPolychrom S χ from ⟨_, this⟩
  intro g k
  obtain ⟨i, hi, hi'⟩ := hχ' (φ g) k
  aesop

lemma canonical_min_zero {n : ℕ} (hn : n ≠ 0)
    (h : ∀ S : Finset ℤ, #S = n → Minimal (· ∈ S) 0 → HasPolychromColouring K S) :
    ∀ S : Finset ℤ, #S = n → HasPolychromColouring K S := by
  intro S hS
  obtain ⟨d, hd⟩ : ∃ i, Minimal (· ∈ S) i := by
    apply Finset.exists_minimal
    rw [← Finset.card_pos]
    simp [hS, pos_iff_ne_zero, hn]
  wlog hd₀ : d = 0 generalizing S d
  · suffices HasPolychromColouring K (-d +ᵥ S) by simpa
    apply this ((-d) +ᵥ S) (by simpa) 0 _ rfl
    simpa [Minimal, Finset.mem_vadd_finset, neg_add_eq_sub, sub_eq_zero] using hd
  cases hd₀
  exact h S hS hd

end
