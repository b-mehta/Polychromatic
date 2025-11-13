import Mathlib

open Finset

variable {ι α : Type*} {s : Finset ι} {p f : ι → α} {c : α} [LinearOrder α]

theorem markov [DivisionSemiring α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hf : ∀ i ∈ s, 0 ≤ f i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ f i, p i ≤ (∑ i ∈ s, p i * f i) / c := by
  rw [le_div_iff₀ hc]
  calc
    (∑ i ∈ s with c ≤ f i, p i) * c = ∑ i ∈ s with c ≤ f i, p i * c := by rw [sum_mul]
    _ ≤ ∑ i ∈ s with c ≤ f i, p i * f i := sum_le_sum fun i hi ↦ by
      simp only [mem_filter] at hi
      exact mul_le_mul_of_nonneg_left hi.2 (hp _ hi.1)
    _ ≤ ∑ i ∈ s, p i * f i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun i hi _ ↦ mul_nonneg (hp i hi) (hf i hi)

theorem markov_abs [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * |f i|) / c :=
  markov hp (by simp) hc

theorem chebyshev [DivisionRing α] [IsStrictOrderedRing α]
    (hp : ∀ i ∈ s, 0 ≤ p i) (hc : 0 < c) :
    ∑ i ∈ s with c ≤ |f i|, p i ≤ (∑ i ∈ s, p i * f i ^ 2) / c ^ 2 := by
  convert markov (f := (f · ^ 2)) hp (c := c ^ 2) (by simp [sq_nonneg]) (by positivity) using 4
  rw [sq_le_sq, abs_of_pos hc]
