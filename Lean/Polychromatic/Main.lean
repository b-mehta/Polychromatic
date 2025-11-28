import Polychromatic.Existence
import Polychromatic.PolychromNumber
import Polychromatic.FourThree.Compute

/-!
# Main Theorem

This file contains the main theorem of the formalization: every set of 4 integers
admits a 3-polychromatic colouring.

## Main results

* `final_result`: Every set `S` of 4 integers has a 3-polychromatic colouring.

## Proof structure

The proof combines:
1. Computational verification for small cases (quadruples with `c < 289`)
2. Explicit interval colourings for larger cases
-/

/-- All quadruples with c < 289 have 3-polychromatic colourings. -/
theorem small_case : ∀ (a b c : ℤ), 0 < a → a < b → b < c → c < 289 →
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_flip _ (suffices_gcd _ (suffices_nat _ (allC_289)))

/-- All ordered quadruples have 3-polychromatic colourings. -/
theorem all_ordered_quadruples (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_cases 289 small_case large_case a b c ha hab hbc

-- ANCHOR: final
/-- Every set `S` of 4 integers has a 3-polychromatic colouring. -/
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S :=
  suffices_minimal (suffices_triple all_ordered_quadruples) S hS
-- ANCHOR_END: final
