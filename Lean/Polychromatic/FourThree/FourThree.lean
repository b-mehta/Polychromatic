import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Algebra.Subalgebra.Basic

import Polychromatic.PolychromNumber
import Polychromatic.FourThree.Theory

open Finset

lemma accept_3_0 (a b c : ℕ) (hb : (b.mod 3).beq 1) (hc : (c.mod 3).beq 2) : Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc])

lemma accept_3_1 (a b c : ℕ) (hb : (b.mod 3).beq 2) (hc : (c.mod 3).beq 1) : Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc, Finset.insert_subset_iff])

lemma accept_3_2 (a b c : ℕ) (ha : (a.mod 3).beq 1) (hc : (c.mod 3).beq 2) : Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])

lemma accept_3_3 (a b c : ℕ) (ha : (a.mod 3).beq 2) (hc : (c.mod 3).beq 1) : Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])

lemma accept_3_4 (a b c : ℕ) (ha : (a.mod 3).beq 1) (hb : (b.mod 3).beq 2) : Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])

lemma accept_3_5 (a b c : ℕ) (ha : (a.mod 3).beq 2) (hb : (b.mod 3).beq 1) : Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])

lemma allA_of_3_0 (A b c : ℕ) (hb : (b.mod 3).beq 1) (hc : (c.mod 3).beq 2) : allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_0 a b c hb hc

lemma allA_of_3_1 (A b c : ℕ) (hb : (b.mod 3).beq 2) (hc : (c.mod 3).beq 1) : allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_1 a b c hb hc

abbrev myOtherType (q aq bq cq : ℕ) (χ : ZMod q → Fin 3) : Prop :=
  IsPolychrom ({0, ↑aq, ↑bq, ↑cq} : Finset (ZMod q)) χ

-- 0,1,3,4;6;1,2,1,2,3,3,
-- 0,2,3,5;4;1,2,1,3,
-- 0,1,3,6;4;1,2,1,3,
-- 0,2,3,6;7;1,2,1,2,3,1,3,
-- 0,1,4,6;9;1,2,2,2,3,3,3,1,1,
-- 0,1,3,7;9;1,2,2,3,1,1,2,3,3,
-- 0,1,4,7;9;1,2,1,2,1,2,3,3,3,
-- 0,3,4,7;6;1,2,1,2,3,3,
-- 0,1,6,7;4;1,2,1,3,

-- 3 bit vectors to represent the colours, check they're pairwise disjoint (· &&& · = 0)
-- &&& with each translation of toBitVector


-- def ofBitVector (n : ℕ) : List ℕ :=
--   (List.range 32).filter (fun i ↦ (n &&& (1 <<< i)) ≠ 0)

-- #eval toBitVectorK 1 3 4

-- #eval toBitVector [1, 3, 4]
-- #eval 0b11010
-- #eval ofBitVector 26

-- #check Nat.shiftLeft
-- #check Nat.lor
-- def spinAux (x : ℕ) (k : ℕ) (i : ℕ) : ℕ := (x <<< i) ||| x >>> (k - i)

-- #eval 0b11010 <<< 2
-- #eval 0b11010 >>> 2
-- #eval ofBitVector (spinAux (toBitVector [0, 1, 4, 6]) 9 8)

-- example : ModAccept 6 1 3 4 := by
--   sorry        n

section

open Lean Expr Meta

def mkColourVector (l : Array (Fin 3)) (x : Fin 3) : Nat :=
  l.foldr (init := 0) fun k i ↦ Nat.bit (k == x) i

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
    let x := mkColourVector l 0
    let y := mkColourVector l 1
    let z := mkColourVector l 2
    let v' : ℕ := toBitVector a b c
    let v : ℕ := v' ||| (v' <<< q)
    let fn : Fin l.size → Fin 3 := fun i ↦ l[i]
    let χ : Expr := toExpr fn
    let nm : Name := .mkSimple s!"accept_{q}_{a%q}_{b%q}_{c%q}"
    let pf := mkApp9 (mkConst ``mainProof)
      (mkRawNatLit q) (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c)
      (mkRawNatLit v) (mkRawNatLit v') (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit z)
    let pf := mkApp8 pf reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      reflBoolTrue reflBoolTrue reflBoolTrue
    let pf ← mkAuxLemma []
      (mkApp4 (mkConst ``ModAccept)
        (mkRawNatLit q) (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c)) pf
      (some nm)
    table := table.insert (q, a, b, c) pf
  trace[debug] "size of table is {table.size}"
  return (table, entries)

def proveAccept (a b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr := do
  if b % 3 = 1 ∧ c % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_0)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
  if b % 3 = 2 ∧ c % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_1)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 1 ∧ c % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_2)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 2 ∧ c % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_3)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 1 ∧ b % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_4)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 2 ∧ b % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_5)
      (mkNatLit a) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue

  let ind ← get
  let some q := entries[ind]?
    | throwError "ran out of entries at {ind}; only have {entries.size}"
  set (ind + 1)
  let (aq, bq, cq) := (a % q, b % q, c % q)
  let some nm := table.get? (q, aq, bq, cq)
    | throwError "no entry for {q} {aq} {bq} {cq}"
  let pf := mkApp6 (mkConst nm) (mkNatLit a) (mkNatLit b) (mkNatLit c)
    reflBoolTrue reflBoolTrue reflBoolTrue
  return pf

def prove_allA (A b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr :=
  match A with
  | 0 => return mkApp2 (mkConst ``allA_zero) (mkNatLit b) (mkNatLit c)
  | 1 => return mkApp2 (mkConst ``allA_one) (mkNatLit b) (mkNatLit c)
  | A + 1 => do
    if b % 3 = 1 ∧ c % 3 = 2 then
      return mkApp5 (mkConst ``allA_of_3_0)
        (mkNatLit (A + 1)) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
    if b % 3 = 2 ∧ c % 3 = 1 then
      return mkApp5 (mkConst ``allA_of_3_1)
        (mkNatLit (A + 1)) (mkNatLit b) (mkNatLit c) reflBoolTrue reflBoolTrue
    let pf_rec ← prove_allA A b c table entries
    let g : ℕ := A.gcd (b.gcd c)
    if g ≠ 1 then
      let pf := mkAppN (mkConst ``allA_succ_of_gcd) #[mkNatLit A, mkNatLit (A + 1), mkNatLit b,
        mkNatLit c,
        mkNatLit g, mkNatLit (A / g), mkNatLit (b / g), mkNatLit (c / g),
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, pf_rec]
      return pf
    else
      let pf_a ← proveAccept A b c table entries
      let pf := mkApp5 (mkConst ``allA_succ_of_accept)
        (mkNatLit A) (mkNatLit b) (mkNatLit c) pf_a pf_rec
      return pf

def prove_allB (B c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr :=
  match B with
  | 0 => return mkApp (mkConst ``allB_zero) (mkNatLit c)
  | 1 => return mkApp (mkConst ``allB_one) (mkNatLit c)
  | 2 => return mkApp (mkConst ``allB_two) (mkNatLit c)
  | B + 1 => do
    if B ≤ c - B + 1 then
      let pf_b ← prove_allB B c table entries
      let pf_a ← prove_allA B B c table entries
      let pf := mkApp6 (mkConst ``allB_succ) (mkNatLit B) (mkNatLit (B + 1)) (mkNatLit c)
        reflBoolTrue pf_a pf_b
      return pf
    else
      let pf_b ← prove_allB B c table entries
      let pf_a ← prove_allA (c - B + 1) B c table entries
      let pf := mkApp8 (mkConst ``allB_succ') (mkNatLit (c - B + 1)) (mkNatLit B) (mkNatLit (B + 1))
        (mkNatLit c) reflBoolTrue reflBoolTrue pf_a pf_b
      return pf

def prove_allC (C : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr :=
  match C with
  | 0 => return mkConst ``allC_zero
  | 1 => return mkConst ``allC_one
  | 2 => return mkConst ``allC_two
  | 3 => return mkConst ``allC_three
  | C + 1 => do
    let pf_c ← prove_allC C table entries
    let pf_b ← prove_allB C C table entries
    let pf := mkApp5 (mkConst ``allC_succ) (mkNatLit C) (mkNatLit (C + 1)) reflBoolTrue pf_b pf_c
    return pf

elab "prove_allC" i:(num)? : tactic => Elab.Tactic.liftMetaFinishingTactic fun g ↦ do
  let t ← g.getType
  match_expr t with
  | allC C => do
    let some C := C.nat? | throwError "no"
    let (table, entries) ← mkTable (i.elim 0 TSyntax.getNat)
    let e ← (prove_allC C table entries).eval 0
    g.assign e
  | _ => throwError "not an allC goal"

end

set_option diagnostics true

lemma allC_289 : allC 10 := by
  prove_allC 90
