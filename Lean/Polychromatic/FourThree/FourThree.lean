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

lemma accept_3_0 (a b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc])

lemma accept_3_1 (a b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper hb, helper hc, Finset.insert_subset_iff])

lemma accept_3_2 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])

lemma accept_3_3 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hc, Finset.insert_subset_iff])

lemma accept_3_4 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 1)) (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])

lemma accept_3_5 (a b c : ℕ)
    (ha : (a.mod (nat_lit 3)).beq (nat_lit 2)) (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) :
    Accept a b c :=
  accept_of_three (by simp [helper ha, helper hb, Finset.insert_subset_iff])

lemma allA_of_3_0 (A b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 1)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 2)) :
    allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_0 a b c hb hc

lemma allA_of_3_1 (A b c : ℕ)
    (hb : (b.mod (nat_lit 3)).beq (nat_lit 2)) (hc : (c.mod (nat_lit 3)).beq (nat_lit 1)) :
    allA A b c := by
  intro a _ _ _ _ _
  apply accept_3_1 a b c hb hc

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

def mkTable (tot : ℕ) : MetaM (Std.HashMap (ℕ × ℕ × ℕ × ℕ) Lean.Name × Array ℕ) :=
  withTraceNode `allC (fun _ ↦ return "mkTable") do
  let i ← IO.FS.lines "../Generation/full-colors.log"
  let i := i.take tot
  withTraceNode `allC (fun _ ↦ return "loop") do
  let mut entries : Array ℕ := #[]
  let mut table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Lean.Name := {}
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
    let v : ℕ := toDoubleBitVector q a b c
    let pf := mkApp8 (mkConst ``mainProof)
      (mkRawNatLit q) (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c)
      (mkRawNatLit v) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit z)
    let pf := mkApp7 pf reflBoolTrue reflBoolTrue reflBoolTrue reflBoolTrue
      reflBoolTrue reflBoolTrue reflBoolTrue
    let pf ← mkAuxLemma []
      (mkApp4 (mkConst ``ModAccept)
        (mkRawNatLit q) (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c)) pf
    table := table.insert (q, a, b, c) pf
  trace[debug] "size of table is {table.size}"
  return (table, entries)

def proveAccept (a b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr := do
  if b % 3 = 1 ∧ c % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_0)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
  if b % 3 = 2 ∧ c % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_1)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 1 ∧ c % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_2)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 2 ∧ c % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_3)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 1 ∧ b % 3 = 2 then
    return mkApp5 (mkConst ``accept_3_4)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
  if a % 3 = 2 ∧ b % 3 = 1 then
    return mkApp5 (mkConst ``accept_3_5)
      (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue

  let ind ← get
  let some q := entries[ind]?
    | throwError "ran out of entries at {ind}; only have {entries.size}"
  set (ind + 1)
  let (aq, bq, cq) := (a % q, b % q, c % q)
  let some nm := table.get? (q, aq, bq, cq)
    | throwError "no entry for {q} {aq} {bq} {cq}"
  let pf := mkApp6 (mkConst nm) (mkRawNatLit a) (mkRawNatLit b) (mkRawNatLit c)
    reflBoolTrue reflBoolTrue reflBoolTrue
  return pf

def prove_allA (A b c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr :=
  match A with
  | 0 => return mkApp2 (mkConst ``allA_zero) (mkRawNatLit b) (mkRawNatLit c)
  | 1 => return mkApp2 (mkConst ``allA_one) (mkRawNatLit b) (mkRawNatLit c)
  | A + 1 => do
    if b % 3 = 1 ∧ c % 3 = 2 then
      return mkApp5 (mkConst ``allA_of_3_0)
        (mkRawNatLit (A + 1)) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
    if b % 3 = 2 ∧ c % 3 = 1 then
      return mkApp5 (mkConst ``allA_of_3_1)
        (mkRawNatLit (A + 1)) (mkRawNatLit b) (mkRawNatLit c) reflBoolTrue reflBoolTrue
    let pf_rec ← prove_allA A b c table entries
    let g : ℕ := A.gcd (b.gcd c)
    if g ≠ 1 then
      let pf := mkAppN (mkConst ``allA_succ_of_gcd) #[mkRawNatLit A, mkRawNatLit b,
        mkRawNatLit c,
        mkRawNatLit g, mkRawNatLit (A / g), mkRawNatLit (b / g), mkRawNatLit (c / g),
        reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, pf_rec]
      return pf
    else
      let pf_a ← proveAccept A b c table entries
      let pf := mkApp5 (mkConst ``allA_succ_of_accept)
        (mkRawNatLit A) (mkRawNatLit b) (mkRawNatLit c) pf_a pf_rec
      return pf

def prove_allB (B c : ℕ) (table : Std.HashMap (ℕ × ℕ × ℕ × ℕ) Name) (entries : Array ℕ) :
    StateT ℕ MetaM Expr :=
  match B with
  | 0 => return mkApp (mkConst ``allB_zero) (mkRawNatLit c)
  | 1 => return mkApp (mkConst ``allB_one) (mkRawNatLit c)
  | 2 => return mkApp (mkConst ``allB_two) (mkRawNatLit c)
  | B + 1 => do
    if B ≤ c - B + 1 then
      let pf_b ← prove_allB B c table entries
      let pf_a ← prove_allA B B c table entries
      let pf := mkApp4 (mkConst ``allB_succ) (mkRawNatLit B) (mkRawNatLit c)
        pf_a pf_b
      return pf
    else
      let pf_b ← prove_allB B c table entries
      let pf_a ← prove_allA (c - B + 1) B c table entries
      let pf := mkApp6 (mkConst ``allB_succ') (mkRawNatLit (c - B + 1)) (mkRawNatLit B)
        (mkRawNatLit c) reflBoolTrue pf_a pf_b
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
    let pf := mkApp3 (mkConst ``allC_succ) (mkRawNatLit C) pf_b pf_c
    return pf

elab "prove_allC" i:(num)? : tactic => Elab.Tactic.liftMetaFinishingTactic fun g ↦ do
  let t ← g.getType
  match_expr t with
  | allC C => do
    let some C := C.nat? | throwError "no"
    let (table, entries) ← mkTable (i.elim 0 TSyntax.getNat)
    withTraceNode `allC (fun _ ↦ return "thing") do
    let e ← (prove_allC C table entries).eval 0
    let nm ← mkAuxLemma [] (mkApp (mkConst ``allC) (mkRawNatLit C)) e
    g.assign (mkConst nm)
  | _ => throwError "not an allC goal"

end

set_option diagnostics true

-- set_option trace.profiler.useHeartbeats true
-- set_option trace.profiler true
-- set_option trace.profiler.threshold 2

-- lemma allC_10 : allC 8 := by
--   prove_allC 90

-- #print allC_10._proof_1_75
