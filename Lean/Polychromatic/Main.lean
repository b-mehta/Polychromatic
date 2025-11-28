import Polychromatic.Existence
import Polychromatic.PolychromNumber
import Polychromatic.FourThree.Compute

/-!
# Main Theorem

This file contains the main theorem of the formalization: every set of 4 integers
admits a 3-polychromatic colouring.

## Main results

* `final_result`: Every set `S` of 4 integers has a 3-polychromatic colouring.

## Proof Sketch

The proof follows Theorem 1 from Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot,
and Young (arXiv:1704.00042). The structure is:

1. **Reduction to canonical form**: Via `suffices_minimal` and `suffices_triple`, we reduce
   to proving the result for sets {0, a, b, c} with 0 < a < b < c and gcd(a,b,c) = 1.

2. **Small case (c < 289)**: Verified computationally via `allC_289`. For each such set,
   there exists a periodic 3-colouring of Z_q for some q that witnesses polychromaticity.

3. **Large case (c ≥ 289)**: Let m = c - a + b. By Lemma 12 (parts ii and iii), it suffices
   to 3-colour Z_m so that translates of S' = {0, b-a, b, 2b-a} are polychromatic.
   The key observation is that S' has two repeated differences: (b-a) and b.

   Define d₁ = gcd(b, m) and d₂ = gcd(b-a, m). Since gcd(a,b,c) = 1, we have gcd(d₁, d₂) = 1.

   **Main Case 1 (Single Cycle)**: min{d₁, d₂} = 1.
   Without loss of generality, assume d₁ = 1. Find g such that gb ≡ b-a (mod m),
   so S' = {0, 1, g, g+1}. Let s be the smallest multiple of 3 such that g > ⌈m/s⌉.
   The proof splits into subcases:
   - (1a) g = 2, 3, or 4: handled by subcase (1c)
   - (1b) 5 ≤ g < 2⌊m/s⌋: split Z_m into s intervals, colour 010101..., 121212..., 202020...
   - (1c) m = 3g + k for -2 ≤ k ≤ 5: explicit colourings for each residue class of m mod 6
   - (1d) m = 3g or 3g + 3: separate construction

   **Main Case 2 (Multiple Cycles)**: min{d₁, d₂} > 1.
   Partition Z_m into cycles and colour each cycle appropriately.
-/

open Finset in
/-! ## Small Case: Computational Verification -/

/-- Small case: all quadruples with c < 289 have 3-polychromatic colourings.
This follows from computational verification using periodic colourings. -/
theorem small_case : ∀ (a b c : ℤ), 0 < a → a < b → b < c → c < 289 →
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_flip _ (suffices_gcd _ (suffices_nat _ (allC_289)))

/-! ## Large Case: Explicit Colourings for c ≥ 289 -/

section LargeCase

/-!
### Lemma 12: Reductions for the Large Case

These lemmas reduce the problem of finding an S-polychromatic colouring of Z to finding
one on Z_m for appropriate m. The key is Lemma 12 from the paper.
-/

/-- Lemma 12(ii): The polychromatic number in Z is at least that in Z_q.
This follows from the homomorphism Z → Z_q (Lemma 9 in the paper). -/
lemma polychromNumber_Zmod_le (S : Finset ℤ) (q : ℕ) [NeZero q] :
    polychromNumber (S.image (Int.cast : ℤ → ZMod q)) ≤ polychromNumber S := by
  sorry

/-- Lemma 12(iii) is in PolychromNumber.lean as `polychromNumber_zmod_le` (note lowercase). -/

/-- For c ≥ 289, the transformed set S' = {0, b-a, b, 2b-a} in Z_m (where m = c-a+b)
has a 3-polychromatic colouring. -/
lemma large_case_transformed (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hc : 289 ≤ c) (hgcd : Finset.gcd {a, b, c} id = 1) :
    let m := (c - a + b).toNat
    HasPolychromColouring (Fin 3)
      (({0, b - a, b, 2 * b - a} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

/-- Main Case 1: Single Cycle (min{d₁, d₂} = 1).

When gcd(b, m) = 1 or gcd(b-a, m) = 1, we can reduce to colouring translates of {0, 1, g, g+1}
for some g with 2 ≤ g ≤ m/2. The proof splits into subcases:
- (1a) g ∈ {2, 3, 4}: handled by explicit colourings in subcase (1c)
- (1b) 5 ≤ g < 2⌊m/s⌋: interval colourings with pattern 010101..., 121212..., 202020...
- (1c) m ≈ 3g: explicit colourings for each residue class of m mod 6
- (1d) m = 3g or 3g + 3: separate constructions -/
lemma single_cycle_case (m g : ℕ) (hm : 0 < m) (hg : 2 ≤ g) (hgm : g ≤ m / 2) :
    HasPolychromColouring (Fin 3)
      (({0, 1, g, g + 1} : Finset ℕ).image (Nat.cast : ℕ → ZMod m)) := by
  sorry

/-- Main Case 2: Multiple Cycles (min{d₁, d₂} > 1).

When both gcd(b, m) > 1 and gcd(b-a, m) > 1, partition Z_m into cycles of length m/dᵢ
for one of the choices of i, and colour each cycle appropriately. -/
lemma multiple_cycle_case (a b c : ℤ) (m : ℕ) (hm : m = (c - a + b).toNat)
    (d₁ d₂ : ℕ) (hd₁ : d₁ = Nat.gcd b.toNat m) (hd₂ : d₂ = Nat.gcd (b - a).toNat m)
    (hmin : 1 < min d₁ d₂) :
    HasPolychromColouring (Fin 3)
      (({0, b - a, b, 2 * b - a} : Finset ℤ).image (Int.cast : ℤ → ZMod m)) := by
  sorry

end LargeCase

/-! ## Large Case: Main Theorem -/

/-- For c ≥ 289, the set {0, a, b, c} has a 3-polychromatic colouring.

The proof uses Lemma 12 to reduce to colouring Z_m where m = c - a + b,
then handles the single cycle and multiple cycle cases. -/
theorem large_case (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : 289 ≤ c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} := by
  sorry

/-! ## Combining Small and Large Cases -/

/-- All ordered quadruples 0 < a < b < c have 3-polychromatic colourings. -/
theorem all_ordered_quadruples (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_cases 289 small_case large_case a b c ha hab hbc

/-! ## Main Theorem -/

-- ANCHOR: final
/-- Every set `S` of 4 integers has a 3-polychromatic colouring. -/
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S :=
  suffices_minimal (suffices_triple all_ordered_quadruples) S hS
-- ANCHOR_END: final
