import Polychromatic.Existence
import Polychromatic.PolychromNumber
import Polychromatic.Compute

-- example : ∀ (a b c : ℤ), 0 < a → a < b → b < c → c < 289 →
--     HasPolychromColouring (Fin 3) {0, a, b, c} :=
--   suffices_flip _ (suffices_gcd _ (suffices_nat _ (allC_289)))

-- ANCHOR: final
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S := by
  sorry
-- ANCHOR_END: final
