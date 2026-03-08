import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Mathlib.Algebra.Ring.AddAut

/-!
# Scratch file: testing interval arithmetic lemmas for Case 1b
-/

-- Two "consecutive-color pairs" with different phases cover all 3 colors
lemma two_pairs_cover (j₁ j₂ : ℕ) (hne : j₁ % 3 ≠ j₂ % 3)
    (k : ℕ) (hk : k < 3) :
    k = j₁ % 3 ∨ k = (j₁ + 1) % 3 ∨ k = j₂ % 3 ∨ k = (j₂ + 1) % 3 := by
  have hj₁ : j₁ % 3 < 3 := Nat.mod_lt _ (by omega)
  have hj₂ : j₂ % 3 < 3 := Nat.mod_lt _ (by omega)
  have : j₁ % 3 = 0 ∨ j₁ % 3 = 1 ∨ j₁ % 3 = 2 := by omega
  have : j₂ % 3 = 0 ∨ j₂ % 3 = 1 ∨ j₂ % 3 = 2 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j₁ % 3 = 0 ∨ _› with h1 | h1 | h1 <;>
  rcases ‹j₂ % 3 = 0 ∨ _› with h2 | h2 | h2 <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega

-- Phase differs when gap is 1 or 2 mod s, and 3 | s
lemma phase_ne_of_gap {s j₀ jg : ℕ} (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by
  obtain ⟨t, ht⟩ := hs3
  subst ht
  -- Now s = 3 * t; clear the divisibility variable
  rcases hgap with h | h
  · -- gap ≡ 1 (mod 3t)
    have hrange : jg + 3 * t - j₀ = 1 ∨ jg + 3 * t - j₀ = 3 * t + 1 := by
      have h1 : 1 ≤ jg + 3 * t - j₀ := by omega
      have h2 : jg + 3 * t - j₀ ≤ 2 * (3 * t) - 1 := by omega
      have h3 : ∃ k, jg + 3 * t - j₀ = k * (3 * t) + 1 := by
        exact ⟨(jg + 3 * t - j₀) / (3 * t), by omega⟩
      obtain ⟨k, hk⟩ := h3
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> omega
    rcases hrange with h1 | h1
    · -- wrapping: j₀ = 3t - 1, jg = 0
      have : j₀ = 3 * t - 1 := by omega
      have : jg = 0 := by omega
      subst ‹jg = 0›
      rw [‹j₀ = 3 * t - 1›]
      have : t ≥ 1 := by omega
      have : 3 * t - 1 = 3 * (t - 1) + 2 := by omega
      rw [this, Nat.mul_add_mod]; omega
    · -- non-wrapping: jg = j₀ + 1
      omega
  · -- gap ≡ 2 (mod 3t)
    have hrange : jg + 3 * t - j₀ = 2 ∨ jg + 3 * t - j₀ = 3 * t + 2 := by
      have h1 : 1 ≤ jg + 3 * t - j₀ := by omega
      have h2 : jg + 3 * t - j₀ ≤ 2 * (3 * t) - 1 := by omega
      have h3 : ∃ k, jg + 3 * t - j₀ = k * (3 * t) + 2 := by
        exact ⟨(jg + 3 * t - j₀) / (3 * t), by omega⟩
      obtain ⟨k, hk⟩ := h3
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> omega
    rcases hrange with h1 | h1
    · -- wrapping case: j₀ = 3t-2, jg=0 or j₀ = 3t-1, jg=1
      have : (j₀ = 3 * t - 2 ∧ jg = 0) ∨ (j₀ = 3 * t - 1 ∧ jg = 1) := by
        omega
      rcases this with ⟨hj₀, hjg⟩ | ⟨hj₀, hjg⟩
      · rw [hjg, hj₀]
        have : t ≥ 1 := by omega
        have : 3 * t - 2 = 3 * (t - 1) + 1 := by omega
        rw [this, Nat.mul_add_mod]; omega
      · rw [hjg, hj₀]
        have : t ≥ 1 := by omega
        have : 3 * t - 1 = 3 * (t - 1) + 2 := by omega
        rw [this, Nat.mul_add_mod]; omega
    · -- non-wrapping: jg = j₀ + 2
      omega

-- Straddle coverage: shared color (j+1)%3 plus non-straddling pair in
-- interval at phase (j+2)%3 covers all 3 colors.
-- j is the interval where straddling occurs, d is the parity of pair 2's
-- first element's offset.
lemma straddle_cover (j d k : ℕ) (hk : k < 3) (hd : d < 2) :
    k = (j + 1) % 3 ∨ k = (j + 2 + d) % 3 ∨ k = (j + 2 + 1 - d) % 3 := by
  have : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have : d = 0 ∨ d = 1 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j % 3 = 0 ∨ _› with hj | hj | hj <;>
  rcases ‹d = 0 ∨ _› with hd' | hd' <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega

-- Symmetric version: non-straddling pair 1 in interval j₀,
-- straddling pair 2 at boundary j₀+1 / j₀+2.
-- Pair 1 contributes {j₀%3, (j₀+1)%3}, pair 2 contributes (j₀+2)%3.
lemma pair_plus_straddle (j d k : ℕ) (hk : k < 3) (hd : d < 2) :
    k = (j + d) % 3 ∨ k = (j + 1 - d) % 3 ∨ k = (j + 2) % 3 := by
  have : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have : d = 0 ∨ d = 1 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j % 3 = 0 ∨ _› with hj | hj | hj <;>
  rcases ‹d = 0 ∨ _› with hd' | hd' <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega
