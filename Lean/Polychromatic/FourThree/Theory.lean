import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

import Polychromatic.PolychromNumber

open Finset

section

lemma suffices_minimal
    (h : ∀ S : Finset ℤ, #S = 4 → Minimal (· ∈ S) 0 → HasPolychromColouring (Fin 3) S):
    ∀ S : Finset ℤ, #S = 4 → HasPolychromColouring (Fin 3) S :=
  canonical_min_zero (by simp) h

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

end

lemma allC_zero : allC 0 := by grind [allC]
lemma allC_one : allC 1 := by grind [allC, allB]
lemma allC_two : allC 2 := by grind [allC, allB, allA]
lemma allC_three : allC 3 := by grind [allC, allB, allA]

lemma allC_succ (C C' : ℕ) (hC' : C'.beq C.succ) (hb : allB C C) (hC : allC C) : allC C' := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq] at hC'
  intro c hc
  obtain hc | rfl : c < C ∨ c = C := by grind
  · exact hC c hc
  · exact hb

lemma allB_zero (c : ℕ) : allB 0 c := by grind [allB]
lemma allB_one (c : ℕ) : allB 1 c := by grind [allB, allA]
lemma allB_two (c : ℕ) : allB 2 c := by grind [allB, allA]

lemma allB_succ (B B' c : ℕ) (hB' : B'.beq B.succ) (ha : allA B B c) (hB : allB B c) :
    allB B' c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq] at hB'
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · exact ha

lemma allB_succ' (A B B' c : ℕ) (hB' : B'.beq B.succ) (hc : c.succ.ble (A.add B)) (ha : allA A B c)
    (hB : allB B c) :
    allB B' c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq] at hB'
  simp only [Nat.add_eq, Nat.ble_eq] at hc
  intro b hbB hbc
  obtain hbB | rfl : b < B ∨ b = B := by grind
  · exact hB _ hbB hbc
  · rintro a ha0 hab - habc hgcd
    exact ha a ha0 hab (by cutsat) habc hgcd

lemma allA_zero (b c : ℕ) : allA 0 b c := by grind [allA]
lemma allA_one (b c : ℕ) : allA 1 b c := by grind [allA]

lemma allA_succ (A b c : ℕ) (h : Accept A b c ∨ A.gcd (b.gcd c) ≠ 1) (hA : allA A b c) :
    allA (A + 1) b c := by
  intro a ha0 hab haA habc hgcd
  obtain haA | rfl : a < A ∨ a = A := by grind
  · exact hA a ha0 hab haA habc hgcd
  grind

lemma allA_succ_of_gcd (A A' b c g ga gb gc : ℕ) (hga : A.beq (ga.mul g)) (hgb : b.beq (gb.mul g))
    (hg : Nat.ble 2 g)
    (hgc : c.beq (gc.mul g)) (hA' : A'.beq A.succ) (hA : allA A b c) :
    allA A' b c := by
  simp only [Nat.mul_eq, Nat.beq_eq, Nat.succ_eq_add_one, Nat.ble_eq] at hga hgb hgc hA' hg
  substs hga hgb hgc hA'
  apply allA_succ _ _ _ _ hA
  right
  rw [Nat.gcd_mul_right, Nat.gcd_mul_right]
  intro h
  have := Nat.eq_one_of_mul_eq_one_left h
  omega

lemma allA_succ_of_accept (A A' b c : ℕ) (hA' : A'.beq A.succ)
    (h : Accept A b c) (hA : allA A b c) :
    allA A' b c := by
  simp only [Nat.succ_eq_add_one, Nat.beq_eq] at hA'
  rw [hA']
  exact allA_succ A b c (Or.inl h) hA

abbrev ModAccept (q aq bq cq : ℕ) : Prop :=
  ∀ a b c : ℕ, (a.mod q).beq aq → (b.mod q).beq bq → (c.mod q).beq cq → Accept a b c

lemma accept_of_three {a b c : ℕ}
    (h : ({0, 1, 2} : Finset (ZMod 3)) ⊆ {0, (a : ZMod 3), (b : ZMod 3), (c : ZMod 3)}) :
    Accept a b c := by
  rw [Accept, ← le_polychromNumber_iff_hasPolychromColouring (by simp)]
  grw [← polychromNumber_image (Int.castAddHom (ZMod 3))]
  simp only [Int.coe_castAddHom, image_insert, Int.cast_zero, Int.cast_natCast, image_singleton]
  change univ ⊆ _ at h
  simp only [univ_subset_iff] at h
  simp [h]

-- 0,1,3,4;6;1,2,1,2,3,3,
-- 0,2,3,5;4;1,2,1,3,
-- 0,1,3,6;4;1,2,1,3,
-- 0,2,3,6;7;1,2,1,2,3,1,3,
-- 0,1,4,6;9;1,2,2,2,3,3,3,1,1,
-- 0,1,3,7;9;1,2,2,3,1,1,2,3,3,
-- 0,1,4,7;9;1,2,1,2,1,2,3,3,3,
-- 0,3,4,7;6;1,2,1,2,3,3,
-- 0,1,6,7;4;1,2,1,3,

def toBitVector (a b c : ℕ) : ℕ :=
  1 ||| 1 <<< a ||| 1 <<< b ||| 1 <<< c

@[simp] lemma Nat.lor_eq {x y : ℕ} : x.lor y = x ||| y := rfl
@[simp] lemma Nat.land_eq {x y : ℕ} : x.land y = x &&& y := rfl

def toBitVectorK (a b c : ℕ) : ℕ :=
  Nat.lor (Nat.lor (Nat.lor 1 (Nat.shiftLeft 1 a)) (Nat.shiftLeft 1 b)) (Nat.shiftLeft 1 c)

def toDoubleBitVector (q a b c : ℕ) : ℕ :=
  toBitVector a b c ||| (toBitVector a b c <<< q)

def toDoubleBitVectorK (q a b c : ℕ) : ℕ :=
  Nat.lor (toBitVectorK a b c) (Nat.shiftLeft (toBitVectorK a b c) q)

lemma toBitVectorK_eq (a b c : ℕ) : toBitVectorK a b c = toBitVector a b c := rfl
@[simp] lemma toDoubleBitVectorK_eq (q a b c : ℕ) :
    toDoubleBitVectorK q a b c = toDoubleBitVector q a b c := rfl

lemma testBit_toBitVector (a b c i : ℕ) :
    Nat.testBit (toBitVector a b c) i = true ↔ i = 0 ∨ i = a ∨ i = b ∨ i = c := by
  rw [toBitVector]
  grind [Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem Nat.shiftLeft_shiftRight_eq_shiftLeft_of_le {b c : Nat} (h : c ≤ b) (a : Nat) :
    a <<< b >>> c = a <<< (b - c) := by
  obtain ⟨b, rfl⟩ := h.dest
  simp [shiftLeft_eq, Nat.pow_add, shiftRight_eq_div_pow, Nat.mul_left_comm a]

lemma testBit_toDoubleBitVector_shiftRight_sub {q a b c i k : ℕ} (hkq : k ≤ q) :
    Nat.testBit (toDoubleBitVector q a b c >>> (q - k)) i = true ↔
      i = k ∨ i = k + a ∨ i = k + b ∨ i = k + c ∨
        i + q = k ∨ i + q = k + a ∨ i + q = k + b ∨ i + q = k + c := by
  rw [toDoubleBitVector, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight_eq_shiftLeft_of_le (by grind), Nat.sub_sub_self hkq]
  simp [testBit_toBitVector]
  grind

lemma testBit_toDoubleBitVector_shiftRight {q a b c i k : ℕ} (hkq : k ≤ q) :
    Nat.testBit (toDoubleBitVector q a b c >>> (q - k)) i = true →
      (i - k : ZMod q) ∈ ({0, (a : ZMod q), (b : ZMod q), (c : ZMod q)} : Finset (ZMod q)) := by
  rw [testBit_toDoubleBitVector_shiftRight_sub (k := k) hkq]
  simp only [mem_insert, mem_singleton]
  rintro (h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁)
  all_goals
    replace h₁ := congr(($h₁ : ZMod q))
    simp at h₁
    grind

lemma testBit_shiftRight_toDoubleBitVector {q a b c k z : ℕ} (hkq : k ≤ q) (hz : z < 2 ^ q)
    (h : 0 < (toDoubleBitVector q a b c >>> (q - k)) &&& z) :
    ∃ i < q, (i - k : ZMod q) ∈ ({0, (a : ZMod q), (b : ZMod q), (c : ZMod q)} : Finset (ZMod q)) ∧
      z.testBit i = true := by
  simp only [Nat.pos_iff_ne_zero, ne_eq] at h
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  refine ⟨i, ?_, testBit_toDoubleBitVector_shiftRight hkq hi.1, hi.2⟩
  by_contra!
  grw [this] at hz
  · simp [Nat.testBit_lt_two_pow hz] at hi
  · simp

-- q' = q - 1
noncomputable def checkValid (q v x y z : ℕ) : Bool :=
  q.rec true fun i acc ↦
    let v' := v.shiftRight (q.sub i)
    ((Nat.ble 1 (v'.land x)).and' ((Nat.ble 1 (v'.land y)).and' (Nat.ble 1 (v'.land z)))).and' acc

lemma rec_and {q : ℕ} (P : ℕ → Bool) :
    Nat.rec true (fun i acc ↦ (P i).and' acc) q = true ↔ ∀ i < q, P i := by
  induction q with
  | zero => simp
  | succ n ih =>
    dsimp
    rw [Bool.and'_eq_and, Bool.and_eq_true, ih, Nat.forall_lt_succ_right, and_comm]

lemma helper {a q aq : ℕ} (ha : (a.mod q).beq aq) : (a : ZMod q) = aq := by
  simp_all [← ZMod.natCast_mod]

lemma ZMod.cases_of_neZero {q : ℕ} [NeZero q] {P : ZMod q → Prop}
    (h : ∀ r : ℕ, r < q → P r) :
    ∀ z : ZMod q, P z := by
  cases q with
  | zero => simp_all
  | succ q =>
    intro r
    simpa using h r.val (ZMod.val_lt _)

lemma lt_two_pow_of_or {x y n : Nat} (h : x ||| y < 2 ^ n) : x < 2 ^ n := by
  by_contra! hx
  have := h.trans_le hx
  exact this.not_ge Nat.left_le_or

lemma or_lt_two_pow_iff {x y n : Nat} : x ||| y < 2 ^ n ↔ x < 2 ^ n ∧ y < 2 ^ n := by
  constructor
  · intro h
    exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩
  · rintro ⟨hx, hy⟩
    exact Nat.or_lt_two_pow hx hy

lemma mainProof {q a b c v v' x y z : ℕ}
    (hv' : v'.beq (toBitVectorK a b c))
    (hv : v.beq (v'.lor (v'.shiftLeft q)))
    (hq : Nat.ble 1 q)
    (hxy : Nat.beq (x.land y) 0)
    (hxz : Nat.beq (x.land z) 0)
    (hyz : Nat.beq (y.land z) 0)
    (hxyz : ((x.lor y).lor z).succ.ble (Nat.shiftLeft 1 q))
    (hvalid : checkValid q v x y z) :
    ModAccept q a b c := by
  simp only [Nat.shiftLeft_eq', Nat.lor_eq, Nat.beq_eq, Nat.ble_eq, Nat.land_eq,
    Nat.one_shiftLeft, toBitVectorK_eq] at hv hv' hq hxy hxz hyz hxyz
  replace hv : v = toDoubleBitVector q a b c := by
    rw [hv, hv']
    simp [toDoubleBitVector]
  have : NeZero q := ⟨by omega⟩
  intro aq bq cq haq hbq hcq
  rw [Accept]
  let χ (i : ZMod q) : Fin 3 := if x.testBit i.val then 0 else if y.testBit i.val then 1 else 2
  have hχx (i : ZMod q) (hi : x.testBit i.val) : χ i = 0 := by
    simp [χ, hi]
  have hχy (i : ZMod q) (hi : y.testBit i.val) : χ i = 1 := by
    simp only [Fin.isValue, hi, ↓reduceIte, ite_eq_right_iff, zero_ne_one, imp_false,
      Bool.not_eq_true, χ]
    by_contra!
    have : (x &&& y).testBit i.val = true := by grind
    simp [hxy] at this
  have hχz (i : ZMod q) (hi : z.testBit i.val) : χ i = 2 := by
    have : x.testBit i.val ≠ true := by
      intro h
      have : (x &&& z).testBit i.val = true := by grind
      simp [hxz] at this
    have : y.testBit i.val ≠ true := by
      intro h
      have : (y &&& z).testBit i.val = true := by grind
      simp [hyz] at this
    simp_all [χ]
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod q))
  refine ⟨χ, ?_⟩
  simp only [Int.coe_castAddHom, image_insert, Int.cast_zero, Int.cast_natCast, helper haq,
    helper hbq, image_singleton, helper hcq]
  rw [checkValid, rec_and] at hvalid
  apply ZMod.cases_of_neZero
  intro i hi
  specialize hvalid i hi
  simp only [Bool.and'_eq_and, Nat.sub_eq, Nat.shiftRight_eq, Bool.and_eq_true,
    Nat.ble_eq, hv, Nat.land_eq] at hvalid
  simp only [Fin.forall_fin_succ, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    IsEmpty.forall_iff, and_true]
  simp only [Nat.succ_le_iff, or_lt_two_pow_iff] at hxyz
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j, hjq, hj, hjx⟩ :=
      testBit_shiftRight_toDoubleBitVector (by omega) (by grind) hvalid.1
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχx j
    simpa [Nat.mod_eq_of_lt hjq]
  · obtain ⟨j, hjq, hj, hjy⟩ :=
      testBit_shiftRight_toDoubleBitVector (by omega) (by grind) hvalid.2.1
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχy j
    simpa [Nat.mod_eq_of_lt hjq]
  · obtain ⟨j, hjq, hj, hjz⟩ :=
      testBit_shiftRight_toDoubleBitVector (by omega) (by grind) hvalid.2.2
    refine ⟨j - (i : ℕ), hj, ?_⟩
    simp only [add_sub_cancel, Fin.isValue]
    apply hχz j
    simpa [Nat.mod_eq_of_lt hjq]

example : ModAccept 6 1 3 4 :=
  mainProof (v' := 0b011011) (v := 0b011011011011) (x := 0b000101) (y := 0b1010) (z := 0b110000)
    rfl rfl rfl rfl rfl rfl rfl rfl
