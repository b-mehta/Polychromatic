import Polychromatic.Existence
import Polychromatic.PolychromNumber
import Polychromatic.FourThree.Compute
import Polychromatic.FourThree.Combi

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
-/

-- ANCHOR: final
/-- Every set `S` of 4 integers has a 3-polychromatic colouring. -/
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S :=
-- ANCHOR_END: final
  suffices_minimal
    (suffices_triple
      (suffices_flip
        (suffices_gcd
          (suffices_cases _
            (suffices_nat _ allC_289)
          normal_bit)))) _ hS
