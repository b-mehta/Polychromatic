import Polychromatic.FourThree.Compute

/-!
# Main Proof for the Four-Three Problem

This file combines the small case (computational verification) and large case
(explicit colourings) to prove that all ordered quadruples have 3-polychromatic colourings.
-/

open Finset

/-- All quadruples with c < 289 have 3-polychromatic colourings. -/
theorem small_case : ∀ (a b c : ℤ), 0 < a → a < b → b < c → c < 289 →
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_flip _ (suffices_gcd _ (suffices_nat _ (allC_289)))

/-- All ordered quadruples have 3-polychromatic colourings. -/
theorem all_ordered_quadruples (a b c : ℤ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    HasPolychromColouring (Fin 3) {0, a, b, c} :=
  suffices_cases 289 small_case large_case a b c ha hab hbc
