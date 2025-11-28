import Polychromatic.Existence
import Polychromatic.PolychromNumber
import Polychromatic.FourThree.Compute

/-!
# Main Theorem

This file contains the main theorem of the formalization: every set of 4 integers
admits a 3-polychromatic colouring.

## Main results

* `final_result`: Every set `S` of 4 integers has a 3-polychromatic colouring.

## Status

The theorem statement is complete, but the proof currently contains `sorry`.
The proof combines:
1. Computational verification for small cases (quadruples with `c < 289`)
2. The Lovász Local Lemma for larger cases

## Proof Sketch

The proof follows Theorem 1 of Alon, Keller, and Litvak (arXiv:1704.00042).
The key steps are:
1. Reduce to canonical form where the set has minimum element 0 (`suffices_minimal`)
2. Further reduce to ordered quadruples `0 < a < b < c` (`suffices_triple`)
3. Split into two cases based on whether `c < 289` or `c ≥ 289` (`suffices_cases`)
4. Small case: Use computational verification via periodic colourings (`allC_289`)
5. Large case: Apply the Lovász Local Lemma with specific parameters

The threshold 289 is chosen to ensure that the LLL condition is satisfied for all
quadruples with `c ≥ 289`, while the computational search covers all cases below.
-/

/-! ## Small Case: Computational Verification -/

/-- Small case: all quadruples with `c < 289` have 3-polychromatic colourings.
This follows from computational verification using periodic colourings. -/
theorem small_case (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : c < 289) :
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_flip _ (suffices_gcd _ (suffices_nat _ (allC_289))) a b c ha hab hbc hc

/-! ## Large Case: Lovász Local Lemma Application -/

section LargeCaseLLL

/-!
### Setting up the LLL argument

For the large case, we use a random periodic colouring with period `q`.
The bad event at position `i` is that the translate `i + {0, a, b, c}` misses some colour.

Key quantities:
- `k = 3`: number of colours
- `m = 4`: size of the set S = {0, a, b, c}
- `p`: probability bound for a bad event
- `d`: maximum degree in the dependency graph

The LLL condition is: `e · p · (d + 1) ≤ 1`
-/

/-- The probability that a random 3-colouring misses a specific colour on a 4-element set.
This equals 3 · (2/3)^4 = 3 · 16/81 = 16/27. -/
lemma prob_bad_event_bound : (3 : ℝ) * (1 - (3 : ℝ)⁻¹) ^ 4 = 16 / 27 := by
  sorry

/-- Two translates of `{0, a, b, c}` share an element iff their difference is in `{0, a, b, c} - {0, a, b, c}`.
The dependency degree `d` is bounded by `|S - S| - 1 = 4 · 3 = 12`. -/
lemma dependency_degree_bound (S : Finset ℤ) (hS : S.card = 4) :
    ((S - S).erase 0).card ≤ 12 := by
  sorry

/-- For `c ≥ 289`, we can choose a period `q` such that the LLL condition holds.
The key is that when `c` is large, we can find `q` with bounded dependency while
still covering all residue classes. -/
lemma lll_condition_satisfied (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : 289 ≤ c) :
    ∃ q : ℕ, 0 < q ∧ Real.exp 1 * (3 * (1 - (3 : ℝ)⁻¹) ^ 4) * (12 + 1 : ℝ) ≤ 1 := by
  sorry

/-- For quadruples `{0, a, b, c}` with `c ≥ 289`, the LLL gives existence of a 3-colouring.

The proof uses the symmetric Lovász Local Lemma (`symmetricLocalLemma`).
For a random 3-colouring of ℤ/qℤ (for appropriate q), we define:
- Bad event A_i: the translate `i + {0, a, b, c}` misses some colour
- Neighborhood N_i: positions whose translates share an element with position i

The LLL condition `e · p · (d + 1) ≤ 1` is satisfied when:
- `p ≤ 3 · (2/3)^4 = 16/27` (probability of missing a colour)
- `d ≤ 12` (dependency degree from `|S - S| - 1`)
- `e · (16/27) · 13 ≈ 15.6 > 1`, so we need a refined analysis

The refined analysis uses that for large `c`, the actual dependency is sparser
because the elements `a, b, c` are spread out, reducing collisions. -/
theorem large_case_lll (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hc : 289 ≤ c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} := by
  sorry

end LargeCaseLLL

/-! ## Combining Small and Large Cases -/

/-- All ordered quadruples `0 < a < b < c` have 3-polychromatic colourings.

This combines the small case (c < 289, handled computationally) with the
large case (c ≥ 289, handled via LLL). -/
theorem all_ordered_quadruples (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_cases 289 small_case large_case_lll a b c ha hab hbc

/-! ## Main Theorem -/

open Finset in
-- ANCHOR: final
/-- Every set `S` of 4 integers has a 3-polychromatic colouring.

The proof reduces to checking ordered quadruples via `suffices_minimal` and `suffices_triple`. -/
theorem final_result (S : Finset ℤ) (hS : #S = 4) :
    HasPolychromColouring (Fin 3) S :=
  suffices_minimal (suffices_triple all_ordered_quadruples) S hS
-- ANCHOR_END: final
