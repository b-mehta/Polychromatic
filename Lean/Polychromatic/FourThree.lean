import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

import Polychromatic.PolychromNumber

open Finset

lemma suffices_minimal
    (h : ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S):
    ∀ S : Finset ℤ, #S = 4 → HasPolychromColouring (Fin 3) S :=
  canonical_min_zero (by simp) h

theorem Minimal.le {α : Type*} [LinearOrder α] {P : α → Prop} {x : α} (y : α)
    (hx : Minimal P x) (hy : P y) : x ≤ y := by
  simpa using not_lt_iff_le_imp_ge.2 (hx.2 hy)

lemma suffices_triple
    (h : ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S := by
  intro S hS hS'
  have : #(S.erase 0) = 3 := by rw [card_erase_of_mem hS'.1, hS]
  rw [card_eq_three] at this
  obtain ⟨a, b, c, hab, hac, hbc, hS0⟩ := this
  have : S = {0, a, b, c} := by rw [← insert_erase hS'.1, hS0]
  wlog hab : a < b generalizing a b
  · apply this b a (by grind) (by grind) (by grind) (by grind) (by grind)
    order
  wlog hac : a < c generalizing a c
  · apply this a c (by grind) (by grind) (by grind) (by grind) (by grind)
    · order
    · order
  wlog hbc : b < c generalizing b c
  · apply this c b (by grind) (by grind) (by grind) (by grind) (by grind)
    · order
    · order
    · order
  have : 0 < a := lt_of_le_of_ne' (hS'.le _ (by grind)) (by grind)
  grind

lemma suffices_cases (C : ℕ)
    (h₁ : ∀ a b c : ℤ, 0 < a → a < b → b < c → c < C → HasPolychromColouring (Fin 3) {0, a, b, c})
    (h₂ : ∀ a b c : ℤ, 0 < a → a < b → b < c → C ≤ c → HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → b < c → HasPolychromColouring (Fin 3) {0, a, b, c} := by
  grind

lemma suffices_flip (C : ℕ)
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → b < c → c < C → HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hcc
  by_cases hsum : a + b ≤ c
  · exact h a b c ha hab hsum hcc
  rw [← hasPolychromColouring_neg, ← hasPolychromColouring_vadd (n := c)]
  suffices HasPolychromColouring (Fin 3) {0, c - b, c - a, c} by
    simp only [neg_insert, neg_zero, neg_singleton, vadd_finset_insert, vadd_eq_add, add_zero,
      ← sub_eq_add_neg, vadd_finset_singleton, sub_self]
    convert this using 1
    grind
  grind

lemma gcd_pos {ι : Type*} {f : ι → ℤ} {s : Finset ι} (hf : ∃ i ∈ s, f i ≠ 0) : 0 < s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp at hf
  | cons a s has ih =>
    classical
    rw [cons_eq_insert, gcd_insert, ← Int.coe_gcd, Int.natCast_pos]
    simp only [Int.gcd_pos_iff, ne_eq]
    simp only [cons_eq_insert, mem_insert, ne_eq, exists_eq_or_imp] at hf
    grind

lemma suffices_gcd (C : ℕ)
    (h : ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c}) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hcc
  let d := Finset.gcd {a, b, c} id
  obtain hd | hd := eq_or_ne d 1
  · exact h a b c ha hab hbc hcc hd
  have hd₀ : 0 < d := gcd_pos ⟨a, by simp, ha.ne'⟩
  let a' := a / d
  let b' := b / d
  let c' := c / d
  have h' : ({a', b', c'} : Finset ℤ) = ({a, b, c} : Finset ℤ).image (fun x ↦ x / d) := by
    simp [a', b', c']
  have : Finset.gcd {a', b', c'} id = 1 := by
    rw [h', ← Finset.gcd_eq_gcd_image]
    exact Finset.gcd_div_eq_one (α := ℤ) (i := a) (by simp) ha.ne'
  have h'' : ({a, b, c} : Finset ℤ) = ({a', b', c'} : Finset ℤ).image (d • ·) := by
    rw [h', image_image, image_congr, image_id]
    intro i hi
    simp only [Finset.mem_coe] at hi
    dsimp
    rw [Int.mul_ediv_cancel']
    apply Finset.gcd_dvd hi
  have : ({0, a, b, c} : Finset ℤ) = ({0, a', b', c'} : Finset ℤ).image (d • ·) := by
    rw [image_insert, smul_zero, h'']
  rw [this]
  rw [← le_polychromNumber_iff_hasPolychromColouring (by simp), polychromNumber_zsmul hd₀.ne',
    le_polychromNumber_iff_hasPolychromColouring (by simp)]
  refine h _ _ _
    (Int.ediv_pos_of_pos_of_dvd ha hd₀.le (Finset.gcd_dvd (by simp)))
    ?_ ?_ ?_ ‹_›
  · simp only [a', b']
    rw [Int.ediv_lt_ediv_iff_of_dvd_of_pos hd₀ hd₀, mul_comm]
    · gcongr
    · apply Finset.gcd_dvd (by simp)
    · apply Finset.gcd_dvd (by simp)
  · simp only [a', b', c']
    rw [← Int.add_ediv_of_dvd_left]
    swap
    · exact Finset.gcd_dvd (by simp)
    apply Int.ediv_le_ediv hd₀ hbc
  · simp only [c']
    grw [Int.ediv_le_self]
    · exact hcc
    · cutsat

def Accept (a b c : ℕ) : Prop :=
  HasPolychromColouring (Fin 3) {0, (a : ℤ), (b : ℤ), (c : ℤ)}

@[simp] lemma Nat.mod_eq' {a b : ℕ} : a.mod b = a % b := rfl

lemma accept_of_three (a b c : ℕ)
    (h : ({0, 1, 2} : Finset (ZMod 3)) ⊆ {0, (a : ZMod 3), (b : ZMod 3), (c : ZMod 3)}) :
    Accept a b c := by
  rw [Accept, ← le_polychromNumber_iff_hasPolychromColouring (by simp)]
  grw [← polychromNumber_image (Int.castAddHom (ZMod 3))]
  simp only [Int.coe_castAddHom, image_insert, Int.cast_zero, Int.cast_natCast, image_singleton]
  change univ ⊆ _ at h
  simp only [univ_subset_iff] at h
  simp [h]

lemma accept_3_0 (a b c : ℕ) (hb : (b.mod 3).beq 1) (hc : (c.mod 3).beq 2) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at hb hc
  replace hb : (b : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, hb]
  replace hc : (c : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, hc]
  apply accept_of_three
  simp [hb, hc]

lemma accept_3_1 (a b c : ℕ) (hb : (b.mod 3).beq 2) (hc : (c.mod 3).beq 1) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at hb hc
  replace hb : (b : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, hb]
  replace hc : (c : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, hc]
  apply accept_of_three
  simp [hb, hc, Finset.insert_subset_iff]

lemma accept_3_2 (a b c : ℕ) (ha : (a.mod 3).beq 1) (hc : (c.mod 3).beq 2) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at ha hc
  replace ha : (a : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, ha]
  replace hc : (c : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, hc]
  apply accept_of_three
  simp [ha, hc, Finset.insert_subset_iff]

lemma accept_3_3 (a b c : ℕ) (ha : (a.mod 3).beq 2) (hc : (c.mod 3).beq 1) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at ha hc
  replace ha : (a : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, ha]
  replace hc : (c : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, hc]
  apply accept_of_three
  simp [ha, hc, Finset.insert_subset_iff]

lemma accept_3_4 (a b c : ℕ) (ha : (a.mod 3).beq 1) (hb : (b.mod 3).beq 2) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at ha hb
  replace ha : (a : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, ha]
  replace hb : (b : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, hb]
  apply accept_of_three
  simp [ha, hb, Finset.insert_subset_iff]

lemma accept_3_5 (a b c : ℕ) (ha : (a.mod 3).beq 2) (hb : (b.mod 3).beq 1) : Accept a b c := by
  simp only [Nat.beq_eq, Nat.mod_eq'] at ha hb
  replace ha : (a : ZMod 3) = 2 := by simp [← ZMod.natCast_mod, ha]
  replace hb : (b : ZMod 3) = 1 := by simp [← ZMod.natCast_mod, hb]
  apply accept_of_three
  simp [ha, hb, Finset.insert_subset_iff]

-- it works for all {0,a,b,c} with a < A
def allA (A : ℕ) (b c : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → a < b → a < A → a + b ≤ c → Nat.gcd a (Nat.gcd b c) = 1 → Accept a b c

-- it works for all {0,a,b,c} with a < b < B
def allB (B : ℕ) (c : ℕ) : Prop := ∀ b : ℕ, b < B → b < c → allA b b c

-- it works for all {0,a,b,c} with a < b < c < C}
def allC (C : ℕ) : Prop := ∀ c : ℕ, c < C → allB c c

lemma suffices_nat (C : ℕ) (h : allC C) :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → c < C → Finset.gcd {a, b, c} id = 1 →
      HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hcc hgcd
  lift a to ℕ using by omega
  lift b to ℕ using by omega
  lift c to ℕ using by omega
  simp only [gcd_insert, id_eq, gcd_singleton, Int.normalize_coe_nat, ← Int.coe_gcd,
    Int.gcd_natCast_natCast, Nat.cast_eq_one] at hgcd
  exact h c (by omega) b (by omega) (by omega) a (by omega) (by omega) (by omega) (by omega) hgcd
  -- exact h c (by omega) b (by omega) a (by omega) (by omega) (by omega) hgcd

lemma allC_zero : allC 0 := by grind [allC]
lemma allC_one : allC 1 := by grind [allC, allB]
lemma allC_two : allC 2 := by grind [allC, allB, allA]
lemma allC_three : allC 3 := by grind [allC, allB, allA]

lemma allC_succ (C : ℕ) (hb : allB C C) (hC : allC C) : allC (C + 1) := by
  intro c hc
  obtain hc | rfl : c < C ∨ c = C := by grind
  · exact hC c hc
  · exact hb

lemma allB_zero (c : ℕ) : allB 0 c := by grind [allB]
lemma allB_one (c : ℕ) : allB 1 c := by grind [allB, allA]
lemma allB_two (c : ℕ) : allB 2 c := by grind [allB, allA]

lemma allB_succ (B c : ℕ) (ha : allA B B c) (hB : allB B c) : allB (B + 1) c := by
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · exact ha

lemma allB_succ' (A B c : ℕ) (hc : c.blt (A.add B)) (ha : allA A B c) (hB : allB B c) :
    allB (B + 1) c := by
  simp only [Nat.add_eq, Nat.blt_eq] at hc
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · rintro a ha0 hab - habc hgcd
    exact ha a ha0 hab (by cutsat) habc hgcd

lemma allA_of_3_0 (A b c : ℕ) (hb : (b.mod 3).beq 1) (hc : (c.mod 3).beq 2) : allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_0 a b c hb hc

lemma allA_of_3_1 (A b c : ℕ) (hb : (b.mod 3).beq 2) (hc : (c.mod 3).beq 1) : allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_1 a b c hb hc

lemma allA_zero (b c : ℕ) : allA 0 b c := by grind [allA]
lemma allA_one (b c : ℕ) : allA 1 b c := by grind [allA]

-- should never need to call when c < A + b
lemma allA_succ (A b c : ℕ) (h : Accept A b c ∨ A.gcd (b.gcd c) ≠ 1) (hA : allA A b c) :
    allA (A + 1) b c := by
  intro a ha0 hab haA habc hgcd
  obtain haA | rfl : a < A ∨ a = A := by grind
  · exact hA a ha0 hab haA habc hgcd
  grind

lemma allA_succ_of_gcd (A A' b c g ga gb gc : ℕ) (hga : A.beq (ga.mul g)) (hgb : b.beq (gb.mul g))
    (hg : Nat.blt 1 g)
    (hgc : c.beq (gc.mul g)) (hA' : A'.beq A.succ) (hA : allA A b c) :
    allA A' b c := by
  simp only [Nat.mul_eq, Nat.beq_eq, Nat.succ_eq_add_one, Nat.blt_eq] at hga hgb hgc hA' hg
  substs hga hgb hgc hA'
  apply allA_succ _ _ _ _ hA
  right
  rw [Nat.gcd_mul_right, Nat.gcd_mul_right]
  intro h
  exact hg.ne' (Nat.eq_one_of_mul_eq_one_left h)

lemma allA_succ_of_accept (A b c : ℕ) (h : Accept A b c) (hA : allA A b c) :
    allA A.succ b c := by
  apply allA_succ _ _ _ _ hA
  left
  exact h

-- 0,1,3,4;6;1,2,1,2,3,3,
-- 0,2,3,5;4;1,2,1,3,
-- 0,1,3,6;4;1,2,1,3,
-- 0,2,3,6;7;1,2,1,2,3,1,3,
-- 0,1,4,6;9;1,2,2,2,3,3,3,1,1,
-- 0,1,3,7;9;1,2,2,3,1,1,2,3,3,
-- 0,1,4,7;9;1,2,1,2,1,2,3,3,3,
-- 0,3,4,7;6;1,2,1,2,3,3,
-- 0,1,6,7;4;1,2,1,3,
-- 0,2,3,8;7;1,2,1,3,1,2,3,
-- 0,2,5,8;9;1,2,1,2,1,2,3,3,3,
-- 0,3,5,8;6;1,2,1,2,3,3,
-- 0,1,3,9;7;1,2,1,3,1,2,3,
-- 0,2,3,9;4;1,2,1,3,
-- 0,1,4,9;6;1,2,1,2,3,3,
-- 0,3,4,9;10;1,2,1,1,3,1,3,2,3,2,
-- 0,2,5,9;6;1,2,1,2,3,3,
-- 0,3,5,9;7;1,2,2,1,1,3,3,
-- 0,1,6,9;7;1,2,1,3,1,2,3,
-- 0,2,6,9;12;1,2,2,2,2,3,3,3,3,1,1,1,
-- 0,1,7,9;15;1,2,1,1,1,3,3,3,2,3,3,2,2,2,1,

lemma helper {a q aq : ℕ} (ha : (a.mod q).beq aq) : (a : ZMod q) = aq := by
  simp_all [← ZMod.natCast_mod]

lemma accept_6_1_3_4 (a b c : ℕ)
    (ha : (a.mod 6).beq 1) (hb : (b.mod 6).beq 3) (hc : (c.mod 6).beq 4) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 6))
  suffices HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod 6)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 0, 1, 2, 2], by decide +kernel⟩

lemma accept_4_1_3_2 (a b c : ℕ)
    (ha : (a.mod 4).beq 1) (hb : (b.mod 4).beq 3) (hc : (c.mod 4).beq 2) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 4))
  suffices HasPolychromColouring (Fin 3) ({0, 1, 3, 2} : Finset (ZMod 4)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 0, 2], by decide +kernel⟩

lemma accept_4_2_3_1 (a b c : ℕ)
    (ha : (a.mod 4).beq 2) (hb : (b.mod 4).beq 3) (hc : (c.mod 4).beq 1) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 4))
  suffices HasPolychromColouring (Fin 3) ({0, 2, 3, 1} : Finset (ZMod 4)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 0, 2], by decide +kernel⟩

lemma accept_7_2_3_6 (a b c : ℕ)
    (ha : (a.mod 7).beq 2) (hb : (b.mod 7).beq 3) (hc : (c.mod 7).beq 6) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 7))
  suffices HasPolychromColouring (Fin 3) ({0, 2, 3, 6} : Finset (ZMod 7)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 0, 1, 2, 0, 2], by decide +kernel⟩

lemma accept_9_1_4_6 (a b c : ℕ)
    (ha : (a.mod 9).beq 1) (hb : (b.mod 9).beq 4) (hc : (c.mod 9).beq 6) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 9))
  suffices HasPolychromColouring (Fin 3) ({0, 1, 4, 6} : Finset (ZMod 9)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 1, 1, 2, 2, 2, 0, 0], by decide +kernel⟩

lemma accept_9_1_3_7 (a b c : ℕ)
    (ha : (a.mod 9).beq 1) (hb : (b.mod 9).beq 3) (hc : (c.mod 9).beq 7) :
    Accept a b c := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod 9))
  suffices HasPolychromColouring (Fin 3) ({0, 1, 3, 7} : Finset (ZMod 9)) by
    simpa [helper ha, helper hb, helper hc]
  exact ⟨![0, 1, 1, 2, 0, 0, 1, 2, 2], by decide +kernel⟩

abbrev myType (q aq bq cq : ℕ) : Prop :=
  ∀ a b c : ℕ, (a.mod q).beq aq → (b.mod q).beq bq → (c.mod q).beq cq → Accept a b c

abbrev myOtherType (q aq bq cq : ℕ) (χ : ZMod q → Fin 3) : Prop :=
  IsPolychrom ({0, ↑aq, ↑bq, ↑cq} : Finset (ZMod q)) χ

lemma accepter (q aq bq cq : ℕ) (χ : ZMod ofNat(q+1) → Fin 3)
    (hχ : decide (myOtherType ofNat(q+1) aq bq cq χ)) :
    myType ofNat(q+1) aq bq cq := by
  intro a b c ha hb hc
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod (q+1)))
  suffices HasPolychromColouring (Fin 3)
      {0, (aq : ZMod (q+1)), (bq : ZMod (q+1)), (cq : ZMod (q+1))} by
    simpa [helper ha, helper hb, helper hc]
  simp only [decide_eq_true_eq] at hχ
  exact ⟨χ, hχ⟩

section

open Lean Expr Meta

def mkTable (tot : ℕ) : MetaM (Std.HashMap (ℕ × ℕ × ℕ × ℕ) Lean.Name × Array ℕ) := do
  let mut table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Lean.Name := {}
  let mut entries : Array ℕ := #[]
  let i ← IO.FS.lines "../Generation/full-colors.log"
  let i := i.take tot
  for j in i do
    let [abc, q, l] := j.splitOn ";" | throwError "no ;"
    let q := q.toNat!
    entries := entries.push q
    let [_, a, b, c] := (abc.splitOn ",").map (fun n ↦ n.toNat! % q) | throwError "no abc"
    if table.contains (q, a, b, c) then
      continue
    let l := l.splitOn ","
    let l : Array (Fin 3) :=
      (l.take (l.length - 1)).toArray |>.map String.toNat! |>.map (fun n ↦ Fin.ofNat 3 (n + 2))
    let fn : Fin l.size → Fin 3 := fun i ↦ l[i]
    let χ : Expr := toExpr fn
    let nm : Name := .mkSimple s!"accept_{q}_{a%q}_{b%q}_{c%q}"
    let pf ← mkAuxLemma []
      (mkApp4 (mkConst ``myType) (mkNatLit q) (mkNatLit a) (mkNatLit b) (mkNatLit c))
      (mkApp6 (mkConst ``accepter) (mkNatLit (q-1)) (mkNatLit a) (mkNatLit b) (mkNatLit c)
        χ reflBoolTrue)
      (some nm)
    table := table.insert (q, a, b, c) pf
  trace[debug] "size of table is {table.size}"
  return (table, entries)

def mkAcceptExpr (a b c : ℕ) : Expr :=
  mkApp3 (mkConst ``Accept) (mkNatLit a) (mkNatLit b) (mkNatLit c)

def proveAccept (a b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM (Expr × List MVarId) := do
  if b % 3 = 1 ∧ c % 3 = 2 then
    return (mkApp5 (mkConst ``accept_3_0)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  if b % 3 = 2 ∧ c % 3 = 1 then
    return (mkApp5 (mkConst ``accept_3_1)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  if a % 3 = 1 ∧ c % 3 = 2 then
    return (mkApp5 (mkConst ``accept_3_2)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  if a % 3 = 2 ∧ c % 3 = 1 then
    return (mkApp5 (mkConst ``accept_3_3)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  if a % 3 = 1 ∧ b % 3 = 2 then
    return (mkApp5 (mkConst ``accept_3_4)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  if a % 3 = 2 ∧ b % 3 = 1 then
    return (mkApp5 (mkConst ``accept_3_5)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
  -- for q in [4:30] do
  --   let (aq, bq, cq) := (a % q, b % q, c % q)
  --   let some nm := Table.get? (q, aq, bq, cq)
  --     | continue
  --   let pf := mkApp6 (mkConst nm) (mkNatLit a) (mkNatLit b) (mkNatLit c)
  --     reflBoolTrue reflBoolTrue reflBoolTrue
  --   return (pf, [])
  -- trace[debug] "stuck at {a} {b} {c}"
  -- let g ← mkFreshExprMVar (some (mkAcceptExpr a b c))
  -- return (g, [g.mvarId!])

  let ind ← get
  let some q := entries[ind]?
    | throwError "ran out of entries {ind}"
  set (ind + 1)
  let (aq, bq, cq) := (a % q, b % q, c % q)
  let some nm := table.get? (q, aq, bq, cq)
    | trace[debug] "no entry for {q} {aq} {bq} {cq}"
      let g ← mkFreshExprMVar (some (mkAcceptExpr a b c))
      return (g, [g.mvarId!])
  let pf := mkApp6 (mkConst nm) (mkNatLit a) (mkNatLit b) (mkNatLit c)
    reflBoolTrue reflBoolTrue reflBoolTrue
  return (pf, [])


def prove_allA (A b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM (Expr × List MVarId) :=
  match A with
  | 0 => return (mkApp2 (mkConst ``allA_zero) (mkNatLit b) (mkNatLit c), [])
  | 1 => return (mkApp2 (mkConst ``allA_one) (mkNatLit b) (mkNatLit c), [])
  | A + 1 => do
    if b % 3 = 1 ∧ c % 3 = 2 then
      return (mkApp5 (mkConst ``allA_of_3_0)
        (mkNatLit (A + 1)) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
    if b % 3 = 2 ∧ c % 3 = 1 then
      return (mkApp5 (mkConst ``allA_of_3_1)
        (mkNatLit (A + 1)) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue, [])
    let (pf_rec, l) ← prove_allA A b c table entries
    let g : ℕ := A.gcd (b.gcd c)
    if g ≠ 1 then
      let pf := mkAppN (mkConst ``allA_succ_of_gcd) #[mkNatLit A, mkNatLit (A + 1), mkNatLit b,
        mkNatLit c,
        mkNatLit g, mkNatLit (A / g), mkNatLit (b / g), mkNatLit (c / g),
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, pf_rec]
      return (pf, l)
    else
      let (pf_a, l_a) ← proveAccept A b c table entries
      let pf := mkApp5 (mkConst ``allA_succ_of_accept)
        (mkNatLit A) (mkNatLit b) (mkNatLit c) pf_a pf_rec
      return (pf, l ++ l_a)

def prove_allB (B c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM (Expr × List MVarId) :=
  match B with
  | 0 => return (mkApp (mkConst ``allB_zero) (mkNatLit c), [])
  | 1 => return (mkApp (mkConst ``allB_one) (mkNatLit c), [])
  | 2 => return (mkApp (mkConst ``allB_two) (mkNatLit c), [])
  | B + 1 => do
    if B ≤ c - B + 1 then
      let (pf_b, l_b) ← prove_allB B c table entries
      let (pf_a, l_a) ← prove_allA B B c table entries
      let pf := mkApp4 (mkConst ``allB_succ) (mkNatLit B) (mkNatLit c) pf_a pf_b
      return (pf, l_b ++ l_a)
    else
      let (pf_b, l_b) ← prove_allB B c table entries
      let (pf_a, l_a) ← prove_allA (c - B + 1) B c table entries
      let pf := mkApp6 (mkConst ``allB_succ') (mkNatLit (c - B + 1)) (mkNatLit B)
        (mkNatLit c) reflBoolTrue pf_a pf_b
      return (pf, l_b ++ l_a)

def prove_allC (C : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM (Expr × List MVarId) :=
  match C with
  | 0 => return (mkConst ``allC_zero, [])
  | 1 => return (mkConst ``allC_one, [])
  | 2 => return (mkConst ``allC_two, [])
  | 3 => return (mkConst ``allC_three, [])
  | C + 1 => do
    let (pf_c, l_c) ← prove_allC C table entries
    let (pf_b, l_b) ← prove_allB C C table entries
    let pf := mkApp3 (mkConst ``allC_succ) (mkNatLit C) pf_b pf_c
    return (pf, l_c ++ l_b)

elab "prove_allC" i:(num)? : tactic => Elab.Tactic.liftMetaTactic fun g ↦ do
  let t ← g.getType
  match_expr t with
  | allC C => do
    let some C := C.nat? | throwError "no"
    let (table, entries) ← mkTable (i.elim 0 TSyntax.getNat)
    let (e, ms) ← (prove_allC C table entries).eval 0
    g.assign e
    return ms
  | _ => throwError "not an allC goal"

end
