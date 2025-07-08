import Mathlib

open Finset

lemma Finset.card_le_one_iff_subsingleton {α : Type*} {S : Finset α} :
    #S ≤ 1 ↔ S.toSet.Subsingleton := by
  rw [Finset.card_le_one_iff_subsingleton_coe, ← Set.subsingleton_coe]
  rfl
