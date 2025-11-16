import Polychromatic.Colouring
import Polychromatic.LocalLemma

open Finset

open Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

-- tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
open MeasureTheory ProbabilityTheory

lemma exists_of {k m : ℕ} {S X : Finset G} (hm : #S = m) (hm : 2 ≤ m) (hk : k ≠ 0) :
    ∃ χ : G → Fin k, ∀ x ∈ X, ∀ c : Fin k, ∃ i ∈ x +ᵥ S, χ i = c := by
  let Y : Finset G := X + S
  let Ω := Y → Fin k
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 (by omega)
  let add : X → S → Y := fun x s ↦ ⟨x + s, add_mem_add x.2 s.2⟩
  let A (x : X) : Set Ω := {χ | ∃ c, ∀ s, χ (add x s) ≠ c}
  let D : X → Finset Y := fun x ↦ S.attach.image (fun s ↦ add x s)
  let N : X → Finset X := fun x ↦ X.attach.filter (fun i ↦ x.1 - i.1 ∈ S - S)
  have : IsProbabilityMeasure (uniformOn Set.univ : Measure (Fin k)) :=
    uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
  have : IsProbabilityMeasure (uniformOn Set.univ : Measure (Y → Fin k)) :=
    uniformOn_isProbabilityMeasure Set.finite_univ Set.univ_nonempty
  have hPAN : standardCondition (Measure.pi (fun _ ↦ uniformOn Set.univ)) A N := by
    refine standardCondition_of _ D ?_ (by fun_prop)
      (iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)) ?_
    · simp only [mem_sub, mem_filter, mem_attach, true_and, not_exists, not_and, disjoint_left,
        mem_image, Subtype.exists, forall_exists_index, Subtype.forall, mem_add, Subtype.mk.injEq,
        and_imp, N, Y, D, add]
      rintro x₁ hx₁ x₂ hx₂ hS _ x₃ hx₃ s₁ hs₁ rfl s₂ hs₂ h s₃ hs₃ h'
      exact hS s₂ hs₂ s₃ hs₃ (by grind)
    · rintro x
      refine ⟨A x, MeasurableSet.of_discrete, ?_, rfl⟩
      simp only [DependsOn, coe_image, coe_attach, Set.image_univ, Set.mem_range, Subtype.exists,
        forall_exists_index, Subtype.forall, Subtype.mk.injEq, Set.mem_setOf_eq, eq_iff_iff, D,
        add, A, Ω]
      intro χ₁ χ₂ h
      peel with c s hs
      rw [h _ _ _ hs rfl]
  rw [← uniformOn_pi, Set.pi_univ] at hPAN
  let p : ℝ := k * (1 - (k : ℝ)⁻¹) ^ m
  have := symmetricLocalLemma (fun i ↦ .of_discrete) (by simp; grind) (p := p) (d := m * (m - 1))
    (lopsidedCondition_of_standardCondition hPAN)
  sorry

theorem exists_prime_aux (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ Set.InjOn (fun i : ℕ ↦ (i : ZMod p)) (S : Set ℕ) := by
  obtain ⟨m, hm⟩ := S.bddAbove
  obtain ⟨p, hp : m < p, hp'⟩ := Nat.exists_infinite_primes (m + 1)
  use p, hp'
  intro i hi j hj h
  simp only at h
  apply_fun ZMod.val at h
  rwa [ZMod.val_natCast_of_lt, ZMod.val_natCast_of_lt] at h
  · exact (hm hj).trans_lt hp
  · exact (hm hi).trans_lt hp

theorem exists_prime {S : Finset ℤ} :
    ∃ p : ℕ, p.Prime ∧ Set.InjOn (fun i : ℤ ↦ (i : ZMod p)) (S : Set ℤ) := by
  obtain ⟨m, hm⟩ := S.bddBelow
  generalize hS' : (-m) +ᵥ S = S'
  have hS : S = m +ᵥ S' := by simp [← hS']
  have hS'' : ∀ x ∈ S', 0 ≤ x := by
    simp only [← hS', mem_vadd_finset, vadd_eq_add, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro i hi
    have := hm hi
    omega
  lift S' to Finset ℕ using hS''
  simpa [Set.InjOn, hS, mem_vadd_finset, mem_image, - coe_vadd_finset] using exists_prime_aux S'

theorem exists_colouring {k : ℕ} {S : Finset ℤ} (hm : 4 * k ^ 2 ≤ #S) :
    HasPolychromColouring (Fin k) S := by
  sorry
