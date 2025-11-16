import Polychromatic.Colouring
import Polychromatic.LocalLemma

open Finset

open Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

-- tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
open MeasureTheory ProbabilityTheory

section

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
  have : iIndepFun (· |> ·) (Measure.pi P) := iIndepFun_pi (X := fun i x ↦ x) (by fun_prop)
  have := this.indepFun_finset s t hi (by fun_prop)
  exact this

lemma pi_inter_eq (s t : Set ι) (hi : Disjoint s t)
    (A : Set (s → Ω)) (B : Set (t → Ω)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measure.pi P (s.restrict ⁻¹' A ∩ t.restrict ⁻¹' B) =
      Measure.pi P (s.restrict ⁻¹' A) * Measure.pi P (t.restrict ⁻¹' B) :=
  (indepFun_restrict_restrict_pi hi (P := P)).measure_inter_preimage_eq_mul A B hA hB

end

-- ∀ k : K, ∃ i ∈ n +ᵥ S, χ i = k

lemma exists_of {k m : ℕ} {S X : Finset G} (hm : #S = m) :
    ∃ χ : G → Fin k, ∀ x ∈ X, ∀ c : Fin k, ∃ i ∈ x +ᵥ S, χ i = c := by
  let Y : Finset G := X + S
  let Ω := Y → Fin k
  let A (x : X) : Set Ω := {χ | ∀ c, ∃ i h, χ ⟨x + i, add_mem_add x.2 h⟩ = c}
  let N : X → Finset X := fun x ↦ sorry
  have hPAN : lopsidedCondition (uniformOn Set.univ) A N := by
    intro i T hiT hNT
    sorry
  sorry

#exit

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
