import Polychromatic.Colouring
import Polychromatic.PolychromNumber

/-!
# Scratch file 2: Key lemmas for case_one_interval

These lemmas are about the interval partition and will be used in the
main proof. They are stated without the coloring, just about idx/off.
-/

-- The key coverage lemma: for two "consecutive-phase pairs" with
-- different phases, every k < 3 is covered.
lemma two_pairs_cover (j₁ j₂ : ℕ) (hne : j₁ % 3 ≠ j₂ % 3)
    (k : ℕ) (hk : k < 3) :
    k = j₁ % 3 ∨ k = (j₁ + 1) % 3 ∨ k = j₂ % 3 ∨ k = (j₂ + 1) % 3 := by
  have : j₁ % 3 = 0 ∨ j₁ % 3 = 1 ∨ j₁ % 3 = 2 := by omega
  have : j₂ % 3 = 0 ∨ j₂ % 3 = 1 ∨ j₂ % 3 = 2 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j₁ % 3 = 0 ∨ _› with h1 | h1 | h1 <;>
  rcases ‹j₂ % 3 = 0 ∨ _› with h2 | h2 | h2 <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega

-- Phase difference: if j₂ = (j₁ + 1) % s or (j₁ + 2) % s, and 3 | s,
-- then j₁ % 3 ≠ j₂ % 3.
-- We prove the simpler non-wrapping version first.
lemma phase_ne_add (j₁ : ℕ) (d : ℕ) (hd : d = 1 ∨ d = 2) :
    j₁ % 3 ≠ (j₁ + d) % 3 := by
  rcases hd with rfl | rfl <;> omega

-- For the wrapping version: (j₁ + d) % s has the same mod 3 as j₁ + d
-- when 3 | s.
lemma mod_mod_of_dvd_three (n s : ℕ) (hs3 : 3 ∣ s) :
    n % s % 3 = n % 3 := by
  exact Nat.mod_mod_of_dvd n (by exact_mod_cast hs3)

-- So: if j₂ = (j₁ + d) % s with d ∈ {1, 2} and 3 | s,
-- then j₂ % 3 = (j₁ + d) % 3 ≠ j₁ % 3.
lemma phase_ne_mod_s (j₁ d s : ℕ) (hs3 : 3 ∣ s) (hd : d = 1 ∨ d = 2) :
    j₁ % 3 ≠ ((j₁ + d) % s) % 3 := by
  rw [mod_mod_of_dvd_three _ s hs3]
  exact phase_ne_add j₁ d hd

-- Gap bound lemma: the interval index of (v+g)%m differs from idx(v) by
-- 1 or 2 (mod s).
-- This is the key arithmetic fact. We state it abstractly.
--
-- Given: m = s*q + r, bd = r*(q+1), g > (m+s-1)/s, g < 2*q,
-- and v < m, we need idx((v+g)%m) ∈ {(idx(v)+1)%s, (idx(v)+2)%s}.
--
-- The proof uses:
-- - Each interval has length q or q+1
-- - g > max interval length (= q+1 if r > 0, else q = ceil(m/s))
-- - g < 2 * min interval length (= 2*q)
-- - So v+g skips past interval idx(v) but stays within 2 intervals ahead

-- For the endgame, the coverage fact for straddling case:
-- When pair 1 straddles at j/j+1, pair 2 is in interval j+2 (all 4 positions).
-- Pair 1 contributes (j+1)%3. Pair 2 contributes {(j+2)%3, j%3}.
-- Together: {j%3, (j+1)%3, (j+2)%3} = {0,1,2}.
lemma straddle_plus_pair_cover (j k : ℕ) (hk : k < 3) :
    k = (j + 1) % 3 ∨ k = (j + 2) % 3 ∨ k = j % 3 := by
  have : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j % 3 = 0 ∨ _› with hj | hj | hj <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega
