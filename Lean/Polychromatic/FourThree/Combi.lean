import Polychromatic.Colouring
import Polychromatic.PolychromNumber

open Finset Pointwise

/--
A helper to define the transformed set in ZMod m.
Corresponds to S = {0, b-a, b, 2b-a} in the informal text.
-/
def zmod_set (m : ℕ) (a b : ℤ) : Finset (ZMod m) :=
  ({0, b - a, b, 2 * b - a} : Finset ℤ).image Int.cast

lemma polychromNumber_zmod {a b c : ℤ} {m : ℕ} (hm : m = c - a + b) :
    polychromNumber (({0, a, b, c} : Finset ℤ).image Int.cast : Finset (ZMod m)) =
      polychromNumber (zmod_set m a b) := by
  set S₁ : Finset (ZMod m) := ({0, a, b, c} : Finset ℤ).image Int.cast
  have : zmod_set m a b = (Int.cast (b - a) : ZMod m) +ᵥ S₁ := by
    simp only [image_insert, Int.cast_zero, Int.cast_sub, image_singleton, Int.cast_mul,
      Int.cast_ofNat, vadd_finset_insert, vadd_eq_add, add_zero, sub_add_cancel,
      vadd_finset_singleton, S₁, zmod_set]
    have : (b : ZMod m) - a + c = 0 := by calc
        (b : ZMod m) - a + c = c - a + b := by ring
        _ = ↑(c - a + b : ℤ) := by simp
        _ = (m : ℤ) := by rw [hm]
        _ = 0 := by simp
    rw [this, sub_add_eq_add_sub, ← two_mul]
    ext i
    simp
    tauto
  rw [this, polychromNumber_vadd]

/-! ## Table 1: Block concatenation colorings

For each set S below, blocks of length r and r+1 (prepending 0 to the period-r block)
can be concatenated in any order to produce an S-polychromatic 3-coloring of ℤ_m.
The Frobenius coin problem ensures m can be so expressed when m > r² - r - 1.
Since all uses have m ≥ 289, the bounds below always hold.
-/

section Table1

variable (m : ℕ)

/-- {0,1,2,3}: blocks 012 (r=3), 0012 (r+1=4). Frobenius bound: m > 5. -/
lemma table1_0123 (hm : m ≥ 6) :
    HasPolychromColouring (Fin 3) ({0, 1, 2, 3} : Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  -- Block boundary: first bd positions use length-4 blocks [0,0,1,2],
  -- remaining positions use length-3 blocks [0,1,2].
  set bd := 4 * (m % 3) with hbd_def
  have hbd_le : bd ≤ m := by omega
  -- Define the coloring
  let c (p : ℕ) : ℕ :=
    if p < bd then (if p % 4 ≤ 1 then 0 else p % 4 - 1) else (p - bd) % 3
  -- Basic properties of c
  have hc_lt3 : ∀ p, c p < 3 := by intro p; simp only [c]; split_ifs <;> omega
  have hc0 : c 0 = 0 := by simp only [c]; split_ifs <;> omega
  have hc_m1 : c (m - 1) = 2 := by simp only [c]; split_ifs <;> omega
  have hc_m2 : c (m - 2) = 1 := by simp only [c]; split_ifs <;> omega
  have hc_m3 : c (m - 3) = 0 := by simp only [c]; split_ifs <;> omega
  -- Construct the polychromatic coloring
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k => ?_⟩
  have hv : n.val < m := ZMod.val_lt n
  -- Reduce to: find a ≤ 3 with c((n.val+a) % m) = k.val
  suffices ∃ a : ℕ, a ≤ 3 ∧ c ((n.val + a) % m) = k.val by
    obtain ⟨a, ha_le, hca⟩ := this
    have ha_lt_m : a < m := by omega
    refine ⟨(a : ZMod m), ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 from by omega with
        rfl | rfl | rfl | rfl <;> simp
    · ext
      show c (n + (a : ZMod m)).val = k.val
      have : (n + (a : ZMod m)).val = (n.val + a) % m := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt_m]
      rw [this, hca]
  -- Abbreviate
  set v := n.val with hv_def
  -- Main case split: wrap vs no-wrap
  by_cases hwrap : v + 3 < m
  · -- NO WRAP: all (v+a) % m = v + a for a ≤ 3
    have no_wrap : ∀ a, a ≤ 3 → (v + a) % m = v + a :=
      fun a ha => Nat.mod_eq_of_lt (by omega)
    by_cases hzone : v ≥ bd
    · -- Block-3 zone
      set r := (v - bd) % 3
      have hr_lt : r < 3 := Nat.mod_lt _ (by omega)
      set a := (k.val + 3 - r) % 3
      have ha_lt : a < 3 := Nat.mod_lt _ (by omega)
      refine ⟨a, by omega, ?_⟩
      rw [no_wrap a (by omega)]
      show c (v + a) = k.val
      simp only [c]
      have : ¬ (v + a < bd) := by omega
      rw [if_neg this]
      show (v + a - bd) % 3 = k.val
      have := k.isLt; omega
    · push_neg at hzone
      by_cases hzone2 : v + 3 < bd
      · -- Block-4 zone
        have h_in_bd : ∀ a, a ≤ 3 → v + a < bd := fun a ha => by omega
        set q := v % 4
        have find_a : ∀ kv : ℕ, kv < 3 → ∃ a, a ≤ 3 ∧ c (v + a) = kv := by
          intro kv hkv
          rcases show kv = 0 ∨ kv = 1 ∨ kv = 2 from by omega with rfl | rfl | rfl
          · refine ⟨(4 - q) % 4, by omega, ?_⟩
            have hmod : (v + (4 - q) % 4) % 4 = 0 := by omega
            simp only [c]
            rw [if_pos (h_in_bd _ (by omega)), if_pos (by omega)]
          · refine ⟨(6 - q) % 4, by omega, ?_⟩
            have hmod : (v + (6 - q) % 4) % 4 = 2 := by omega
            simp only [c]
            rw [if_pos (h_in_bd _ (by omega)), if_neg (by omega)]
            omega
          · refine ⟨(7 - q) % 4, by omega, ?_⟩
            have hmod : (v + (7 - q) % 4) % 4 = 3 := by omega
            simp only [c]
            rw [if_pos (h_in_bd _ (by omega)), if_neg (by omega)]
            omega
        obtain ⟨a, ha_le, ha_eq⟩ := find_a k.val k.isLt
        exact ⟨a, ha_le, by rw [no_wrap a ha_le]; exact ha_eq⟩
      · -- Spanning block-4/block-3 boundary: v < bd, v + 3 ≥ bd
        push_neg at hzone2
        have hbd_pos : 0 < bd := by omega
        -- The last 3 of block-4 and first 3 of block-3 give colors 0,1,2,0,1,2
        have hc_boundary : ∀ j, j ≤ 5 → c (bd - 3 + j) = j % 3 := by
          intro j hj
          simp only [c]
          rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 from
            by omega with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> omega
        -- v = bd - 3 + j for some j ≤ 2
        set j := v - (bd - 3)
        have hj_le : j ≤ 2 := by omega
        set a := (k.val + 3 - j % 3) % 3
        have ha_lt : a < 3 := Nat.mod_lt _ (by omega)
        refine ⟨a, by omega, ?_⟩
        rw [no_wrap a (by omega)]
        have hva : v + a = bd - 3 + (j + a) := by omega
        rw [hva, hc_boundary (j + a) (by omega)]
        have := k.isLt; omega
  · -- WRAP case: v ≥ m - 3
    push_neg at hwrap
    have hmod_v : v % m = v := Nat.mod_eq_of_lt hv
    -- v ∈ {m-3, m-2, m-1}
    rcases show v = m - 3 ∨ v = m - 2 ∨ v = m - 1 from by omega
      with hveq | hveq | hveq
    · -- v = m - 3: window {m-3, m-2, m-1, 0}
      have h1 : (v + 1) % m = m - 2 := by
        have : v + 1 = m - 2 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h2 : (v + 2) % m = m - 1 := by
        have : v + 2 = m - 1 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      fin_cases k
      · exact ⟨0, by omega, by rw [add_zero, hmod_v, hveq]; exact hc_m3⟩
      · exact ⟨1, by omega, by rw [h1]; exact hc_m2⟩
      · exact ⟨2, by omega, by rw [h2]; exact hc_m1⟩
    · -- v = m - 2: window {m-2, m-1, 0, 1}
      have h1 : (v + 1) % m = m - 1 := by
        have : v + 1 = m - 1 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h2 : (v + 2) % m = 0 := by
        have : v + 2 = m := by omega
        rw [this, Nat.mod_self]
      fin_cases k
      · exact ⟨2, by omega, by rw [h2]; exact hc0⟩
      · exact ⟨0, by omega, by rw [add_zero, hmod_v, hveq]; exact hc_m2⟩
      · exact ⟨1, by omega, by rw [h1]; exact hc_m1⟩
    · -- v = m - 1: window {m-1, 0, 1, 2}
      have h1 : (v + 1) % m = 0 := by
        have : v + 1 = m := by omega
        rw [this, Nat.mod_self]
      have h2 : (v + 2) % m = 1 := by
        have : v + 2 = 1 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h3 : (v + 3) % m = 2 := by
        have : v + 3 = 2 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      fin_cases k
      · exact ⟨1, by omega, by rw [h1]; exact hc0⟩
      · -- k = 1: depends on m % 3
        by_cases hmod : m % 3 = 0
        · refine ⟨2, by omega, ?_⟩
          rw [h2]; show c 1 = 1
          simp only [c, hbd_def, hmod]; norm_num
        · refine ⟨3, by omega, ?_⟩
          rw [h3]; show c 2 = 1
          simp only [c]; split_ifs <;> omega
      · exact ⟨0, by omega, by rw [add_zero, hmod_v, hveq]; exact hc_m1⟩

/-- {0,1,3,4}: blocks 001212 (r=6), 0001212 (r+1=7). Frobenius bound: m > 29. -/
lemma table1_0134 (hm : m ≥ 30) :
    HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod m)) := by sorry
/-  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  -- Block boundary: first bd positions use length-7 blocks [0,0,0,1,2,1,2],
  -- remaining positions use length-6 blocks [0,0,1,2,1,2].
  set bd := 7 * (m % 6) with hbd_def
  have hbd_le : bd ≤ m := by omega
  -- Define the coloring
  let c (p : ℕ) : ℕ :=
    if p < bd then
      if p % 7 ≤ 2 then 0 else if p % 7 % 2 = 1 then 1 else 2
    else
      let q := (p - bd) % 6
      if q ≤ 1 then 0 else if q % 2 = 0 then 1 else 2
  -- Basic properties of c
  have hc_lt3 : ∀ p, c p < 3 := by intro p; simp only [c]; split_ifs <;> omega
  have hc0 : c 0 = 0 := by simp only [c]; split_ifs <;> omega
  have hc_m1 : c (m - 1) = 2 := by simp only [c]; split_ifs <;> omega
  have hc_m2 : c (m - 2) = 1 := by simp only [c]; split_ifs <;> omega
  have hc_m3 : c (m - 3) = 2 := by simp only [c]; split_ifs <;> omega
  have hc_m4 : c (m - 4) = 1 := by simp only [c]; split_ifs <;> omega
  -- Color values at small positions
  have hc1 : c 1 = 0 := by simp only [c]; split_ifs <;> omega
  have hc2 : c 2 = (if m % 6 = 0 then 1 else 0) := by
    simp only [c]; split_ifs <;> omega
  have hc3 : c 3 = (if m % 6 = 0 then 2 else 1) := by
    simp only [c]; split_ifs <;> omega
  have hc4 : c 4 = (if m % 6 = 0 then 1 else 2) := by
    simp only [c]; split_ifs <;> omega
  -- Construct the polychromatic coloring
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k => ?_⟩
  have hv : n.val < m := ZMod.val_lt n
  -- Reduce to: find a in {0,1,3,4} with c((n.val+a) % m) = k.val
  suffices ∃ a : ℕ, a ∈ ({0, 1, 3, 4} : Finset ℕ) ∧ c ((n.val + a) % m) = k.val by
    obtain ⟨a, ha_mem, hca⟩ := this
    have ha_lt_m : a < m := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with rfl | rfl | rfl | rfl <;> omega
    refine ⟨(a : ZMod m), ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      rcases ha_mem with rfl | rfl | rfl | rfl <;> simp
    · ext
      show c (n + (a : ZMod m)).val = k.val
      have : (n + (a : ZMod m)).val = (n.val + a) % m := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt_m]
      rw [this, hca]
  -- Abbreviate
  set v := n.val with hv_def
  -- Main case split: wrap vs no-wrap
  by_cases hwrap : v + 4 < m
  · -- NO WRAP: all (v+a) % m = v + a for a ≤ 4
    have no_wrap : ∀ a, a ≤ 4 → (v + a) % m = v + a :=
      fun a ha => Nat.mod_eq_of_lt (by omega)
    by_cases hzone : v ≥ bd
    · -- Block-6 zone: entirely in 6-block pattern
      set r := (v - bd) % 6
      have hr_lt : r < 6 := Nat.mod_lt _ (by omega)
      -- All offsets stay in block-6 zone
      have h_in_6 : ∀ a, a ≤ 4 → ¬ (v + a < bd) := fun a _ => by omega
      -- c(v + a) for a ≤ 4 depends on (v + a - bd) % 6
      have hr_eq : ∀ a, a ≤ 4 → (v + a - bd) % 6 = (r + a) % 6 := by
        intro a ha; omega
      -- For each color k, find appropriate a in {0,1,3,4}
      -- r=0: offsets 0,1,3,4 -> (r+a)%6 = 0,1,3,4 -> colors 0,0,2,1
      -- r=1: offsets 0,1,3,4 -> 1,2,4,5 -> 0,1,1,2
      -- r=2: offsets 0,1,3,4 -> 2,3,5,0 -> 1,2,2,0
      -- r=3: offsets 0,1,3,4 -> 3,4,0,1 -> 2,1,0,0
      -- r=4: offsets 0,1,3,4 -> 4,5,1,2 -> 1,2,0,1
      -- r=5: offsets 0,1,3,4 -> 5,0,2,3 -> 2,0,1,2
      have find_a : ∀ kv : ℕ, kv < 3 → ∃ a ∈ ({0, 1, 3, 4} : Finset ℕ),
          c (v + a) = kv := by
        intro kv hkv
        rcases show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 from by omega
          with rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases show kv = 0 ∨ kv = 1 ∨ kv = 2 from by omega
            with rfl | rfl | rfl <;> (
          first
          | exact ⟨0, by simp, by simp only [c]; rw [if_neg (h_in_6 0 (by omega))];
              show (fun q => if q ≤ 1 then 0 else if q % 2 = 0 then 1 else 2)
                ((v + 0 - bd) % 6) = _; rw [hr_eq 0 (by omega)]; simp; omega⟩
          | exact ⟨1, by simp, by simp only [c]; rw [if_neg (h_in_6 1 (by omega))];
              show (fun q => if q ≤ 1 then 0 else if q % 2 = 0 then 1 else 2)
                ((v + 1 - bd) % 6) = _; rw [hr_eq 1 (by omega)]; simp; omega⟩
          | exact ⟨3, by simp, by simp only [c]; rw [if_neg (h_in_6 3 (by omega))];
              show (fun q => if q ≤ 1 then 0 else if q % 2 = 0 then 1 else 2)
                ((v + 3 - bd) % 6) = _; rw [hr_eq 3 (by omega)]; simp; omega⟩
          | exact ⟨4, by simp, by simp only [c]; rw [if_neg (h_in_6 4 (by omega))];
              show (fun q => if q ≤ 1 then 0 else if q % 2 = 0 then 1 else 2)
                ((v + 4 - bd) % 6) = _; rw [hr_eq 4 (by omega)]; simp; omega⟩)
      obtain ⟨a, ha_mem, ha_eq⟩ := find_a k.val k.isLt
      exact ⟨a, ha_mem, by
        rw [no_wrap a (by simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem;
          rcases ha_mem with rfl | rfl | rfl | rfl <;> omega)]
        exact ha_eq⟩
    · push_neg at hzone
      by_cases hzone2 : v + 4 < bd
      · -- Block-7 zone: entirely in 7-block pattern
        have h_in_7 : ∀ a, a ≤ 4 → v + a < bd := fun a ha => by omega
        set r := v % 7
        have hr_lt : r < 7 := Nat.mod_lt _ (by omega)
        have hr_eq : ∀ a, a ≤ 4 → (v + a) % 7 = (r + a) % 7 := by
          intro a ha; omega
        -- r=0: offsets 0,1,3,4 -> 0,1,3,4 -> 0,0,1,2
        -- r=1: offsets 0,1,3,4 -> 1,2,4,5 -> 0,0,2,1
        -- r=2: offsets 0,1,3,4 -> 2,3,5,6 -> 0,1,1,2
        -- r=3: offsets 0,1,3,4 -> 3,4,6,0 -> 1,2,2,0
        -- r=4: offsets 0,1,3,4 -> 4,5,0,1 -> 2,1,0,0
        -- r=5: offsets 0,1,3,4 -> 5,6,1,2 -> 1,2,0,0
        -- r=6: offsets 0,1,3,4 -> 6,0,2,3 -> 2,0,0,1
        have find_a : ∀ kv : ℕ, kv < 3 → ∃ a ∈ ({0, 1, 3, 4} : Finset ℕ),
            c (v + a) = kv := by
          intro kv hkv
          rcases show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6
            from by omega with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases show kv = 0 ∨ kv = 1 ∨ kv = 2 from by omega
              with rfl | rfl | rfl <;> (
            first
            | exact ⟨0, by simp, by simp only [c]; rw [if_pos (h_in_7 0 (by omega))];
                show (if (v + 0) % 7 ≤ 2 then 0
                  else if (v + 0) % 7 % 2 = 1 then 1 else 2) = _;
                rw [hr_eq 0 (by omega)]; simp; omega⟩
            | exact ⟨1, by simp, by simp only [c]; rw [if_pos (h_in_7 1 (by omega))];
                show (if (v + 1) % 7 ≤ 2 then 0
                  else if (v + 1) % 7 % 2 = 1 then 1 else 2) = _;
                rw [hr_eq 1 (by omega)]; simp; omega⟩
            | exact ⟨3, by simp, by simp only [c]; rw [if_pos (h_in_7 3 (by omega))];
                show (if (v + 3) % 7 ≤ 2 then 0
                  else if (v + 3) % 7 % 2 = 1 then 1 else 2) = _;
                rw [hr_eq 3 (by omega)]; simp; omega⟩
            | exact ⟨4, by simp, by simp only [c]; rw [if_pos (h_in_7 4 (by omega))];
                show (if (v + 4) % 7 ≤ 2 then 0
                  else if (v + 4) % 7 % 2 = 1 then 1 else 2) = _;
                rw [hr_eq 4 (by omega)]; simp; omega⟩)
        obtain ⟨a, ha_mem, ha_eq⟩ := find_a k.val k.isLt
        exact ⟨a, ha_mem, by
          rw [no_wrap a (by simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem;
            rcases ha_mem with rfl | rfl | rfl | rfl <;> omega)]
          exact ha_eq⟩
      · -- Spanning block-7/block-6 boundary: v < bd ≤ v + 4
        push_neg at hzone2
        have hbd_pos : 0 < bd := by omega
        -- Near the boundary, the 7-block ends with ...1,2,1,2 and
        -- the 6-block starts 0,0,1,2,1,2.
        -- Positions bd-4..bd+3 have colors 1,2,1,2,0,0,1,2
        have hc_boundary : ∀ j, j ≤ 7 → c (bd - 4 + j) =
            [1, 2, 1, 2, 0, 0, 1, 2].get ⟨j, by simp; omega⟩ := by
          intro j hj
          simp only [c]
          rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
            from by omega with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp <;> split_ifs <;> omega
        -- v is in {bd-4, bd-3, bd-2, bd-1}
        set j := v - (bd - 4)
        have hj_le : j ≤ 3 := by omega
        have hva : ∀ a, a ≤ 4 → v + a = bd - 4 + (j + a) := by intro a _; omega
        -- j=0 (v=bd-4): colors at j,j+1,j+3,j+4 = 1,2,2,0 -> {0,1,2}
        -- j=1 (v=bd-3): 2,1,0,0 -> {0,1,2}
        -- j=2 (v=bd-2): 1,2,0,1 -> {0,1,2}
        -- j=3 (v=bd-1): 2,0,1,2 -> {0,1,2}
        rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 from by omega
          with rfl | rfl | rfl | rfl
        · -- j=0: colors 1,2,2,0
          fin_cases k
          · exact ⟨4, by simp, by rw [no_wrap 4 (by omega), hva 4 (by omega),
              hc_boundary 4 (by omega)]; simp⟩
          · exact ⟨0, by simp, by rw [no_wrap 0 (by omega), hva 0 (by omega),
              hc_boundary 0 (by omega)]; simp⟩
          · exact ⟨1, by simp, by rw [no_wrap 1 (by omega), hva 1 (by omega),
              hc_boundary 1 (by omega)]; simp⟩
        · -- j=1: colors 2,1,0,0
          fin_cases k
          · exact ⟨3, by simp, by rw [no_wrap 3 (by omega), hva 3 (by omega),
              hc_boundary 4 (by omega)]; simp⟩
          · exact ⟨1, by simp, by rw [no_wrap 1 (by omega), hva 1 (by omega),
              hc_boundary 2 (by omega)]; simp⟩
          · exact ⟨0, by simp, by rw [no_wrap 0 (by omega), hva 0 (by omega),
              hc_boundary 1 (by omega)]; simp⟩
        · -- j=2: colors 1,2,0,1
          fin_cases k
          · exact ⟨3, by simp, by rw [no_wrap 3 (by omega), hva 3 (by omega),
              hc_boundary 5 (by omega)]; simp⟩
          · exact ⟨0, by simp, by rw [no_wrap 0 (by omega), hva 0 (by omega),
              hc_boundary 2 (by omega)]; simp⟩
          · exact ⟨1, by simp, by rw [no_wrap 1 (by omega), hva 1 (by omega),
              hc_boundary 3 (by omega)]; simp⟩
        · -- j=3: colors 2,0,1,2
          fin_cases k
          · exact ⟨1, by simp, by rw [no_wrap 1 (by omega), hva 1 (by omega),
              hc_boundary 4 (by omega)]; simp⟩
          · exact ⟨3, by simp, by rw [no_wrap 3 (by omega), hva 3 (by omega),
              hc_boundary 6 (by omega)]; simp⟩
          · exact ⟨0, by simp, by rw [no_wrap 0 (by omega), hva 0 (by omega),
              hc_boundary 3 (by omega)]; simp⟩
  · -- WRAP case: v ≥ m - 4
    push_neg at hwrap
    have hmod_v : v % m = v := Nat.mod_eq_of_lt hv
    -- v in {m-4, m-3, m-2, m-1}
    rcases show v = m - 4 ∨ v = m - 3 ∨ v = m - 2 ∨ v = m - 1 from by omega
      with hveq | hveq | hveq | hveq
    · -- v = m - 4: window {m-4, m-3, m-1, 0}
      have h1 : (v + 1) % m = m - 3 := by
        have : v + 1 = m - 3 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h3 : (v + 3) % m = m - 1 := by
        have : v + 3 = m - 1 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h4 : (v + 4) % m = 0 := by
        have : v + 4 = m := by omega
        rw [this, Nat.mod_self]
      fin_cases k
      · exact ⟨4, by simp, by rw [h4]; exact hc0⟩
      · exact ⟨0, by simp, by rw [add_zero, hmod_v, hveq]; exact hc_m4⟩
      · exact ⟨1, by simp, by rw [h1]; exact hc_m3⟩
    · -- v = m - 3: window {m-3, m-2, 0, 1}
      have h1 : (v + 1) % m = m - 2 := by
        have : v + 1 = m - 2 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h3 : (v + 3) % m = 0 := by
        have : v + 3 = m := by omega
        rw [this, Nat.mod_self]
      have h4 : (v + 4) % m = 1 := by
        have : v + 4 = 1 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      fin_cases k
      · exact ⟨3, by simp, by rw [h3]; exact hc0⟩
      · exact ⟨1, by simp, by rw [h1]; exact hc_m2⟩
      · exact ⟨0, by simp, by rw [add_zero, hmod_v, hveq]; exact hc_m3⟩
    · -- v = m - 2: window {m-2, m-1, 1, 2}
      have h1 : (v + 1) % m = m - 1 := by
        have : v + 1 = m - 1 := by omega
        rw [this]; exact Nat.mod_eq_of_lt (by omega)
      have h3 : (v + 3) % m = 1 := by
        have : v + 3 = 1 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h4 : (v + 4) % m = 2 := by
        have : v + 4 = 2 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      fin_cases k
      · exact ⟨3, by simp, by rw [h3]; exact hc1⟩
      · exact ⟨0, by simp, by rw [add_zero, hmod_v, hveq]; exact hc_m2⟩
      · exact ⟨1, by simp, by rw [h1]; exact hc_m1⟩
    · -- v = m - 1: window {m-1, 0, 2, 3}
      have h1 : (v + 1) % m = 0 := by
        have : v + 1 = m := by omega
        rw [this, Nat.mod_self]
      have h3 : (v + 3) % m = 2 := by
        have : v + 3 = 2 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h4 : (v + 4) % m = 3 := by
        have : v + 4 = 3 + m := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      fin_cases k
      · exact ⟨1, by simp, by rw [h1]; exact hc0⟩
      · -- k = 1: c(2) or c(3) depending on m % 6
        by_cases hmod : m % 6 = 0
        · exact ⟨3, by simp, by rw [h3]; rw [hc2, if_pos hmod]⟩
        · exact ⟨4, by simp, by rw [h4]; rw [hc3, if_neg hmod]⟩
      · exact ⟨0, by simp, by rw [add_zero, hmod_v, hveq]; exact hc_m1⟩
-/

/-- {0,2,3,5}: blocks 001122 (r=6), 0001122 (r+1=7). Frobenius bound: m > 29. -/
lemma table1_0235 (hm : m ≥ 30) :
    HasPolychromColouring (Fin 3) ({0, 2, 3, 5} : Finset (ZMod m)) := by sorry

/-- {0,3,4,7}: blocks 000111222 (r=9), 0000111222 (r+1=10). Frobenius bound: m > 71. -/
lemma table1_0347 (hm : m ≥ 72) :
    HasPolychromColouring (Fin 3) ({0, 3, 4, 7} : Finset (ZMod m)) := by sorry

/-- {0,3,5,8}: blocks 000111222 (r=9), 0000111222 (r+1=10). Frobenius bound: m > 71. -/
lemma table1_0358 (hm : m ≥ 72) :
    HasPolychromColouring (Fin 3) ({0, 3, 5, 8} : Finset (ZMod m)) := by sorry

/-- {0,1,4,5}: blocks 0001212 (r=7), 00001212 (r+1=8). Frobenius bound: m > 41. -/
lemma table1_0145 (hm : m ≥ 42) :
    HasPolychromColouring (Fin 3) ({0, 1, 4, 5} : Finset (ZMod m)) := by sorry

end Table1

section Case1_SingleCycle

variable (m : ℕ)

-- In this section, we work with the affine transformed set {0, 1, g, g+1}.

/-- Subcase (1a): g ∈ {2, 3, 4}.
    Handled by the table constructions in subcase (1c). -/
lemma case_one_small_g (g : ℕ) (hm : m ≥ 289) (hg : g ∈ ({2, 3, 4} : Finset ℕ)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  fin_cases hg <;> push_cast <;> norm_num
  · exact table1_0123 m (by omega)
  · exact table1_0134 m (by omega)
  · exact table1_0145 m (by omega)

/-- Subcase (1b): 5 ≤ g < 2⌊m/s⌋ (specifically s=6 here).
    Handled by the interval coloring strategy (01...12...20...). -/
lemma case_one_interval (g : ℕ) (h_ge : 5 ≤ g) (h_lt : g < 2 * (m / 6)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- Multiplication by a unit in ZMod m is an additive automorphism,
    so it preserves HasPolychromColouring. This is Lemma 12(iv). -/
lemma hasPolychromColouring_mul_unit (u : (ZMod m)ˣ) (S : Finset (ZMod m)) :
    HasPolychromColouring (Fin 3) (S.image (u.val * ·)) ↔
    HasPolychromColouring (Fin 3) S := by
  have key : polychromNumber (S.image (u.val * ·)) = polychromNumber S := by
    let φ : ZMod m ≃+ ZMod m :=
      { toFun := (u.val * ·)
        invFun := (↑u⁻¹ * ·)
        left_inv := fun x => by simp [← mul_assoc, Units.inv_mul]
        right_inv := fun x => by simp [← mul_assoc, Units.mul_inv]
        map_add' := fun x y => mul_add _ _ _ }
    exact polychromNumber_iso φ
  constructor
  · intro h
    exact hasPolychromColouring_fin_of_le (by omega) (key ▸ le_polychromNumber h)
  · intro h
    exact hasPolychromColouring_fin_of_le (by omega) (key.symm ▸ le_polychromNumber h)

-- Subcase (1c) per-residue lemmas: each reduces {0,1,g,g+1} to a Table 1 set
-- via multiplication by 3 (an automorphism of ZMod m when 3 ∤ m) and translation.

/-- m = 3g - 2: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,2,3,5}. -/
lemma case_one_res_3g_sub_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  have hndvd : ¬(3 ∣ m) := by intro ⟨k, hk⟩; omega
  obtain ⟨u, hu⟩ :=
    ZMod.isUnit_prime_of_not_dvd Nat.prime_three hndvd
  rw [← hasPolychromColouring_mul_unit m u
    {0, 1, (g : ZMod m), (g : ZMod m) + 1}]
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = 2 := by
    have : ((3 * g : ℕ) : ZMod m) = ((m + 2 : ℕ) : ZMod m) :=
      by congr 1; omega
    simpa [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      ZMod.natCast_self] using this
  have h3g1_mod :
      (3 : ZMod m) * ((g : ZMod m) + 1) = 5 := by
    have : ((3 * (g + 1) : ℕ) : ZMod m) =
        ((m + 5 : ℕ) : ZMod m) := by congr 1; omega
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, ZMod.natCast_self] using this
  rw [image_insert, image_insert, image_insert,
    image_singleton,
    show u.val = (3 : ZMod m) from hu, mul_zero, mul_one,
    h3g_mod, h3g1_mod]
  rw [show ({0, (3 : ZMod m), 2, 5} : Finset (ZMod m)) =
      {0, 2, 3, 5} from by
    ext x; simp [Finset.mem_insert]; tauto]
  exact table1_0235 m (by omega)

/-- m = 3g - 1: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,1,3,4}. -/
lemma case_one_res_3g_sub_1 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g - 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have hg1 : g ≥ 97 := by omega
  have hndvd : ¬(3 ∣ m) := by
    intro ⟨k, hk⟩; omega
  have h3unit : IsUnit (3 : ZMod m) :=
    ZMod.isUnit_prime_of_not_dvd Nat.prime_three hndvd
  obtain ⟨u, hu⟩ := h3unit
  rw [← hasPolychromColouring_mul_unit m u
    {0, 1, (g : ZMod m), (g : ZMod m) + 1}]
  have h3g : (3 * g : ℕ) = m + 1 := by omega
  have h3g1 : (3 * (g + 1) : ℕ) = m + 4 := by omega
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = 1 := by
    have : ((3 * g : ℕ) : ZMod m) = ((m + 1 : ℕ) : ZMod m) := by
      rw [h3g]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      ZMod.natCast_self, zero_add] at this
    exact this
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 4 := by
    have : ((3 * (g + 1) : ℕ) : ZMod m) = ((m + 4 : ℕ) : ZMod m) := by
      rw [h3g1]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      ZMod.natCast_self, zero_add] at this
    exact this
  show HasPolychromColouring (Fin 3)
    (({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
      Finset (ZMod m)).image (u.val * ·))
  rw [image_insert, image_insert, image_insert, image_singleton,
    show u.val = (3 : ZMod m) from hu, mul_zero, mul_one,
    h3g_mod, h3g1_mod]
  rw [show ({0, (3 : ZMod m), 1, 4} : Finset (ZMod m)) =
      {0, 1, 3, 4} from by ext x; simp [Finset.mem_insert]; tauto]
  exact table1_0134 m (by omega)

/-- m = 3g + 1: ×3 maps {0,1,g,g+1} to {0,3,-1,2}, a translate of {0,1,3,4}. -/
lemma case_one_res_3g_add_1 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have hg1 : g ≥ 96 := by omega
  have hndvd : ¬(3 ∣ m) := by
    intro ⟨k, hk⟩; omega
  have h3unit : IsUnit (3 : ZMod m) :=
    ZMod.isUnit_prime_of_not_dvd Nat.prime_three hndvd
  obtain ⟨u, hu⟩ := h3unit
  rw [← hasPolychromColouring_mul_unit m u
    {0, 1, (g : ZMod m), (g : ZMod m) + 1}]
  have h3g : (3 * g + 1 : ℕ) = m := by omega
  have h3g1 : (3 * (g + 1) : ℕ) = m + 2 := by omega
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = -1 := by
    have : ((3 * g + 1 : ℕ) : ZMod m) = ((m : ℕ) : ZMod m) := by
      rw [h3g]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, ZMod.natCast_self] at this
    -- this : (3 : ZMod m) * (g : ZMod m) + 1 = 0
    exact eq_neg_of_add_eq_zero_left this
  have h3g1_mod :
      (3 : ZMod m) * ((g : ZMod m) + 1) = 2 := by
    have : ((3 * (g + 1) : ℕ) : ZMod m) =
        ((m + 2 : ℕ) : ZMod m) := by
      rw [h3g1]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, ZMod.natCast_self, zero_add] at this
    exact this
  show HasPolychromColouring (Fin 3)
    (({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
      Finset (ZMod m)).image (u.val * ·))
  rw [image_insert, image_insert, image_insert, image_singleton,
    show u.val = (3 : ZMod m) from hu, mul_zero, mul_one,
    h3g_mod, h3g1_mod]
  rw [show ({0, (3 : ZMod m), -1, 2} : Finset (ZMod m)) =
      (-1 : ZMod m) +ᵥ ({0, 1, 3, 4} : Finset (ZMod m)) from by
    simp only [vadd_finset_insert, vadd_finset_singleton,
      vadd_eq_add]
    ext x; simp [Finset.mem_insert]; ring_nf; tauto]
  rw [hasPolychromColouring_vadd]
  exact table1_0134 m (by omega)

/-- m = 3g + 2: ×3 maps {0,1,g,g+1} to {0,3,-2,1}, a translate of {0,2,3,5}. -/
lemma case_one_res_3g_add_2 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- m = 3g + 4: ×3 maps {0,1,g,g+1} to {0,3,-4,-1}, a translate of {0,3,4,7}. -/
lemma case_one_res_3g_add_4 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 4) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- m = 3g + 5: ×3 maps {0,1,g,g+1} to {0,3,-5,-2}, a translate of {0,3,5,8}. -/
lemma case_one_res_3g_add_5 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 5) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- Subcase (1c) assembled: dispatches to the six per-residue lemmas above. -/
lemma case_one_residues (g : ℕ) (hm : m ≥ 289) (h_res : m % 3 ≠ 0)
    (h_range : 2 * (m / 6) ≤ g ∧ g ≤ (m + 2) / 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

-- Subcase (1d) sub-subcases, split by g mod 3.

/-- (1d), g ≢ 0 (mod 3): the periodic coloring 012012...012 works because
    each translate of {0,1,g,g+1} hits all 3 residue classes mod 3. -/
lemma case_one_div_g_not_three (g : ℕ)
    (h_div : m = 3 * g ∨ m = 3 * g + 3)
    (hg3 : g % 3 ≠ 0) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  have h3_dvd : 3 ∣ m :=
    by rcases h_div with rfl | rfl <;> omega
  haveI : NeZero m := ⟨by omega⟩
  -- Map ZMod m → ZMod 3 via the canonical quotient
  apply HasPolychromColouring.of_image
    (ZMod.castHom h3_dvd (ZMod 3))
  -- Image is {0,1,(g:ZMod 3),(g:ZMod 3)+1} = univ
  simp only [Finset.image_insert, Finset.image_singleton,
    map_zero, map_one, map_add, map_natCast]
  -- Since g%3 ≠ 0, the image is all of ZMod 3
  have hg12 : g % 3 = 1 ∨ g % 3 = 2 := by omega
  suffices ({0, 1, (g : ZMod 3), (g : ZMod 3) + 1} :
      Finset (ZMod 3)) = Finset.univ by
    rw [this]; exact hasPolychromColouring_univ
  rcases hg12 with h | h <;> {
    have : (g : ZMod 3) = ↑(g % 3 : ℕ) := by
      rw [ZMod.natCast_mod]
    simp only [this, h]; decide
  }

private lemma case_one_div_3g_no_cross
    (g t : ℕ) (hg : 0 < g) (ht : g = 3 * t)
    (v q r : ℕ) (hr_lt : r < g) (hq_lt : q < 3)
    (hqr : v = q * g + r) (hv_lt : v < 3 * g)
    (hv_mod3 : v % 3 = r % 3)
    (hg_val : (g : ZMod (3 * g)).val = g)
    (h1_val : (1 : ZMod (3 * g)).val = 1)
    (n : ZMod (3 * g)) (hn : n.val = v)
    (hr1 : r + 1 < g) (k : Fin 3) :
    ∃ a ∈ ({0, 1, (g : ZMod (3 * g)),
        (g : ZMod (3 * g)) + 1} : Finset (ZMod (3 * g))),
      (⟨((n + a).val % 3 + (n + a).val / g) % 3,
        Nat.mod_lt _ (by omega)⟩ : Fin 3) = k := by
  sorry


lemma case_one_div_3g (g : ℕ) (hm_eq : m = 3 * g)
    (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  sorry

lemma case_one_div_3g3 (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- Subcase (1d) assembled: dispatches to the three sub-subcases above. -/
lemma case_one_divisible (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  by_cases hg3 : g % 3 = 0
  · rcases h_div with h | h
    · exact case_one_div_3g m g h (Nat.dvd_of_mod_eq_zero hg3) (by omega)
    · exact case_one_div_3g3 m g h (Nat.dvd_of_mod_eq_zero hg3)
  · exact case_one_div_g_not_three m g h_div hg3

/-- Combined dispatch: applies subcases (1a)–(1d) for 2 ≤ g ≤ m/2 and m ≥ 289. -/
lemma case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g) (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  sorry

/-- WLOG g ≤ m/2: in ZMod m, {0,1,m-g,m-g+1} = (-g) +ᵥ {0,1,g,g+1},
    so HasPolychromColouring is preserved. -/
lemma case_one_complement (g : ℕ) (hg : g < m) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (↑(m - g) : ZMod m), (↑(m - g) : ZMod m) + 1} : Finset (ZMod m)) ↔
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have key : (↑(m - g) : ZMod m) = -(↑g : ZMod m) := by
    rw [Nat.cast_sub hg.le, ZMod.natCast_self, zero_sub]
  rw [key]
  conv_lhs =>
    rw [show ({0, 1, -(↑g : ZMod m), -(↑g : ZMod m) + 1} : Finset (ZMod m)) =
        (-(↑g : ZMod m)) +ᵥ ({(↑g : ZMod m), (↑g : ZMod m) + 1, 0, 1} : Finset (ZMod m)) from by
      simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
      ext x; simp [neg_add_cancel]]
  rw [show ({(↑g : ZMod m), (↑g : ZMod m) + 1, 0, 1} : Finset (ZMod m)) =
      ({0, 1, (↑g : ZMod m), (↑g : ZMod m) + 1} : Finset (ZMod m)) from by ext x; simp; tauto]
  exact hasPolychromColouring_vadd

private lemma isUnit_intCast_of_natAbs_coprime {n : ℕ} {b : ℤ}
    (h : Nat.gcd b.natAbs n = 1) :
    IsUnit (Int.cast b : ZMod n) := by
  have hu : IsUnit (b.natAbs : ZMod n) :=
    (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq b with hb | hb
  · rwa [show (Int.cast b : ZMod n) = ↑b.natAbs from by rw [hb]; simp]
  · rw [show (Int.cast b : ZMod n) = -↑b.natAbs from by rw [hb]; simp]
    exact hu.neg

/-- When gcd(b, m) = 1, there exists 2 ≤ g ≤ m - 2 with gb ≡ b - a (mod m),
    and zmod_set m a b = (image of {0,1,g,g+1} under ×b). -/
lemma exists_g_of_coprime (a b : ℤ) (hd : Nat.gcd b.natAbs m = 1)
    (hm : 0 < m) (hcard : (zmod_set m a b).card = 4) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ m - 2 ∧
      zmod_set m a b =
        ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)).image
          ((b : ZMod m) * ·) := by
  -- m ≥ 4 since zmod_set has 4 distinct elements in ZMod m
  have hm4 : 4 ≤ m := by
    haveI : NeZero m := ⟨by omega⟩
    calc 4 = (zmod_set m a b).card := hcard.symm
      _ ≤ Fintype.card (ZMod m) := Finset.card_le_univ _
      _ = m := ZMod.card m
  haveI : NeZero m := ⟨by omega⟩
  -- b is a unit in ZMod m
  have hub : IsUnit ((b : ℤ) : ZMod m) := isUnit_intCast_of_natAbs_coprime hd
  -- Abbreviations for casts
  set bz : ZMod m := (b : ZMod m)
  set az : ZMod m := (a : ZMod m)
  -- Define g' = b⁻¹ * (b - a) in ZMod m
  set g' : ZMod m := bz⁻¹ * (bz - az)
  -- Key identity: b * g' = b - a
  have hbg' : bz * g' = bz - az := by
    show bz * (bz⁻¹ * (bz - az)) = bz - az
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ hub, one_mul]
  -- Consequence: b * (g' + 1) = 2b - a
  have hbg'1 : bz * (g' + 1) = 2 * bz - az := by
    rw [mul_add, mul_one, hbg']; ring
  -- The set equality (with g' as ZMod m element)
  have hset : zmod_set m a b =
      ({0, 1, g', g' + 1} : Finset (ZMod m)).image (bz * ·) := by
    simp only [zmod_set, Finset.image_insert, Finset.image_singleton]
    simp only [mul_zero, mul_one, hbg', hbg'1]
    push_cast
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  -- g'.val is our witness. Since (g'.val : ZMod m) = g', we can substitute.
  have hval : (g'.val : ZMod m) = g' := ZMod.natCast_zmod_val g'
  -- Multiplication by bz is injective (bz is a unit)
  have hinj : Function.Injective (bz * · : ZMod m → ZMod m) := by
    intro x y (hxy : bz * x = bz * y)
    have h1 : bz⁻¹ * (bz * x) = bz⁻¹ * (bz * y) := congr_arg (bz⁻¹ * ·) hxy
    simp only [← mul_assoc, ZMod.inv_mul_of_unit _ hub, one_mul] at h1
    exact h1
  -- Source set has card 4
  have hcard4 : ({0, 1, g', g' + 1} : Finset (ZMod m)).card = 4 := by
    rwa [hset, Finset.card_image_of_injective _ hinj] at hcard
  refine ⟨g'.val, ?_, ?_, ?_⟩
  · -- 2 ≤ g'.val: if g'.val < 2, then g' ∈ {0, 1}, source set has < 4 elements
    by_contra hlt; push_neg at hlt
    have hcases : g'.val = 0 ∨ g'.val = 1 := by omega
    rcases hcases with h | h
    · have hg'0 : g' = 0 := by rw [← hval, h, Nat.cast_zero]
      -- {0, 1, 0, 0+1} ⊆ {0, 1}, card ≤ 2
      have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1} := by
        rw [hg'0, zero_add]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]
      linarith [Finset.card_le_card hsub, Finset.card_le_two (a := (0 : ZMod m)) (b := 1)]
    · have hg'1 : g' = 1 := by rw [← hval, h, Nat.cast_one]
      -- {0, 1, 1, 1+1} ⊆ {0, 1, 1+1}, card ≤ 3
      have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, (1 : ZMod m) + 1} := by
        rw [hg'1]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]
      linarith [Finset.card_le_card hsub,
        Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := (1 : ZMod m) + 1)]
  · -- g'.val ≤ m - 2
    by_contra hgt; push_neg at hgt
    have hval_lt := ZMod.val_lt g'
    have hgm1 : g'.val = m - 1 := by omega
    have hg'p1 : g' + 1 = 0 := by
      rw [← hval, hgm1, Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self, zero_sub,
        neg_add_cancel]
    -- {0, 1, g', 0} ⊆ {0, 1, g'}, card ≤ 3
    have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, g'} := by
      rw [hg'p1]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
    linarith [Finset.card_le_card hsub,
      Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := g')]
  · -- The set equality: substitute g'.val for g'
    conv at hset => rhs; rw [show g' = (g'.val : ZMod m) from hval.symm]
    exact hset

/-- Aggregation of Main Case 1.
    Reduces to {0,1,g,g+1} via exists_g_of_coprime and hasPolychromColouring_mul_unit,
    applies WLOG g ≤ m/2 via case_one_complement,
    then dispatches via case_one_dispatch. -/
lemma main_case_one (a b : ℤ) (hm : m ≥ 289)
    (hcard : (zmod_set m a b).card = 4)
    (h_gcd : Nat.gcd b.natAbs m = 1 ∨ Nat.gcd (b - a).natAbs m = 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  -- Helper: prove HasPolychromColouring given gcd(b, m) = 1 for a general (a, b)
  suffices ∀ a' b' : ℤ, Nat.gcd b'.natAbs m = 1 →
      (zmod_set m a' b').card = 4 →
      HasPolychromColouring (Fin 3) (zmod_set m a' b') by
    rcases h_gcd with hb | hba
    · exact this a b hb hcard
    · -- Use zmod_set_swap: zmod_set m (-a) (b - a) = zmod_set m a b
      have swap : zmod_set m (-a) (b - a) = zmod_set m a b := by
        simp only [zmod_set]
        congr 1
        have h1 : b - a - -a = b := by ring
        have h2 : 2 * (b - a) - -a = 2 * b - a := by ring
        rw [h1, h2]
        simp [insert_comm]
      rw [← swap]
      apply this (-a) (b - a) hba
      rwa [swap]
  intro a' b' hd hcard'
  -- Get g with 2 ≤ g ≤ m - 2 and the set equality
  obtain ⟨g, hg_ge, hg_le, hset⟩ := exists_g_of_coprime m a' b' hd (by omega) hcard'
  -- Show (b' : ZMod m) is a unit
  have hb'_unit : IsUnit (b' : ZMod m) := by
    have hunit : IsUnit (b'.natAbs : ZMod m) :=
      (ZMod.isUnit_iff_coprime _ _).mpr hd
    rcases Int.natAbs_eq b' with h | h
    · rwa [show (b' : ZMod m) = (b'.natAbs : ZMod m) from by rw [h]; simp]
    · rw [show (b' : ZMod m) = -(b'.natAbs : ZMod m) from by rw [h]; simp]
      exact hunit.neg
  obtain ⟨u, hu⟩ := hb'_unit
  rw [hset, ← hu]
  rw [hasPolychromColouring_mul_unit]
  -- Now prove HasPolychromColouring (Fin 3) ({0, 1, g, g+1})
  by_cases hg_half : g ≤ m / 2
  · exact case_one_dispatch m g hm hg_ge hg_half
  · push_neg at hg_half
    rw [← case_one_complement m g (by omega)]
    exact case_one_dispatch m (m - g) hm (by omega) (by omega)

end Case1_SingleCycle

section Case2_MultipleCycles

variable (m : ℕ) (a b : ℤ)

-- In this section, we work directly with `zmod_set` using cycle decompositions.
-- We inline d1 = gcd(b, m) and e1 = m / d1.

/-- Subcase (2a): e1 is even.
    Cycles are colored with alternating 01/02 patterns. -/
lemma case_two_e1_even (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (he1_even : Even (m / Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  sorry

/-- Subcase (2b): d1 is even and e1 is odd.
    Cycles use modified alternating patterns (ending in 11 or 02). -/
lemma case_two_d1_even_e1_odd (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_even : Even (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  sorry

/-- Subcase (2c): d1 and e1 are both odd, with e1 ≤ 17.
    Uses three specific patterns distributed across the cycles. -/
lemma case_two_odd_small (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_odd : Odd (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m))
    (he1_le : m / Nat.gcd b.natAbs m ≤ 17) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  sorry

/-- Subcase (2d): d1 and e1 are both odd, with e1 ≥ 19.
    Uses "rotating" colorings based on partitioning e1 = u + v + w. -/
lemma case_two_odd_large (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_odd : Odd (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m))
    (he1_ge : m / Nat.gcd b.natAbs m ≥ 19) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  sorry

/-- Aggregation of Main Case 2.
    Assumption: min(gcd(b, m), gcd(b-a, m)) > 1.
    Splits into the four subcases based on parity and size of e1. -/
lemma main_case_two (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  rcases Nat.even_or_odd (m / Nat.gcd b.natAbs m) with he | ho
  · exact case_two_e1_even m a b hm h_gcd_coprime h_min he
  · rcases Nat.even_or_odd (Nat.gcd b.natAbs m) with hd | hd
    · exact case_two_d1_even_e1_odd m a b hm h_gcd_coprime h_min hd ho
    · by_cases he_le : m / Nat.gcd b.natAbs m ≤ 17
      · exact case_two_odd_small m a b hm h_gcd_coprime h_min hd ho he_le
      · have : m / Nat.gcd b.natAbs m ≥ 19 := by
          obtain ⟨k, hk⟩ := ho; omega
        exact case_two_odd_large m a b hm h_gcd_coprime h_min hd ho this

end Case2_MultipleCycles

/-- The set {0, b-a, b, 2b-a} is symmetric in the two repeated differences b and b-a:
    swapping them (replacing a by -a, b by b-a) gives the same set. -/
lemma zmod_set_swap (m : ℕ) (a b : ℤ) :
    zmod_set m (-a) (b - a) = zmod_set m a b := by
  simp only [zmod_set]
  congr 1
  have h1 : b - a - -a = b := by ring
  have h2 : 2 * (b - a) - -a = 2 * b - a := by ring
  rw [h1, h2]
  simp [insert_comm]

/-- The set zmod_set m a b has 4 elements when 0 < a < b and 2b - a < m. -/
lemma zmod_set_card_eq_four {a b : ℤ} {m : ℕ}
    (ha : 0 < a) (hab : a < b) (hbm : 2 * b - a < ↑m) :
    (zmod_set m a b).card = 4 := by
  unfold zmod_set
  -- Helper: two integers in [0, m) that cast to the same ZMod m element must be equal
  have hne : ∀ x y : ℤ, 0 ≤ x → x < ↑m → 0 ≤ y → y < ↑m → x ≠ y →
      (x : ZMod m) ≠ (y : ZMod m) := by
    intro x y hx1 hx2 hy1 hy2 hxy h
    exact hxy (by rwa [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hx1 hx2,
                        Int.emod_eq_of_lt hy1 hy2] at h)
  have ne01 := hne 0 (b - a) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ne02 := hne 0 b (by omega) (by omega) (by omega) (by omega) (by omega)
  have ne03 := hne 0 (2 * b - a) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ne12 := hne (b - a) b (by omega) (by omega) (by omega) (by omega) (by omega)
  have ne13 := hne (b - a) (2 * b - a) (by omega) (by omega) (by omega) (by omega) (by omega)
  have ne23 := hne b (2 * b - a) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [image_insert, image_singleton]
  rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · rw [mem_singleton]; exact ne23
  · simp only [mem_insert, mem_singleton]; push_neg; exact ⟨ne12, ne13⟩
  · simp only [mem_insert, mem_singleton]; push_neg; exact ⟨ne01, ne02, ne03⟩

/-- The coprimality gcd(d₁, d₂) = 1 follows from gcd(a, b, c) = 1 and m = c - a + b,
    since gcd(b-a, b, m) = gcd(b-a, b, c-a+b) = gcd(a, b, c). -/
lemma gcd_coprime_of_gcd_abc {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (hgcd : Finset.gcd {a, b, c} id = 1) :
    (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1 := by
  set d := (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) with hd_def
  -- d divides b.natAbs, (b-a).natAbs, and m (as natural numbers)
  have hd_dvd_b : d ∣ b.natAbs :=
    (Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_left _ _)
  have hd_dvd_m : d ∣ m :=
    (Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_right _ _)
  have hd_dvd_ba : d ∣ (b - a).natAbs :=
    (Nat.gcd_dvd_right (Nat.gcd _ _) _).trans (Nat.gcd_dvd_left _ _)
  -- Lift to integer divisibility
  have hd_b : (d : ℤ) ∣ b := Int.natCast_dvd.mpr hd_dvd_b
  have hd_m : (d : ℤ) ∣ ↑m := Int.natCast_dvd_natCast.mpr hd_dvd_m
  have hd_ba : (d : ℤ) ∣ (b - a) := Int.natCast_dvd.mpr hd_dvd_ba
  -- d | a = b - (b - a)
  have hd_a : (d : ℤ) ∣ a := by
    have : a = b - (b - a) := by ring
    rw [this]; exact dvd_sub hd_b hd_ba
  -- d | c = m - b + a  (from m = c - a + b)
  have hd_c : (d : ℤ) ∣ c := by
    have : (c : ℤ) = ↑m - b + a := by linarith
    rw [this]; exact dvd_add (dvd_sub hd_m hd_b) hd_a
  -- (d : ℤ) divides each element of {a, b, c}, hence divides Finset.gcd {a, b, c} id = 1
  have hd_dvd_gcd : (d : ℤ) ∣ Finset.gcd {a, b, c} id :=
    Finset.dvd_gcd (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hd_a
      · exact hd_b
      · exact hd_c)
  rw [hgcd] at hd_dvd_gcd
  exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd_dvd_gcd)

/-- Reduction from HasPolychromColouring on zmod_set to HasPolychromColouring on {0, a, b, c} in ℤ.
    Combines the homomorphism ℤ → ZMod m (Lemma 12(ii)) with the translation
    equivalence (Lemma 12(iii), i.e. `polychromNumber_zmod`). -/
lemma hasPolychromColouring_of_zmod_set {a b c : ℤ} {m : ℕ}
    (hm_eq : (m : ℤ) = c - a + b)
    (h : HasPolychromColouring (Fin 3) (zmod_set m a b)) :
    HasPolychromColouring (Fin 3) ({0, a, b, c} : Finset ℤ) := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod m))
  show HasPolychromColouring (Fin 3)
    (({0, a, b, c} : Finset ℤ).image (Int.cast : ℤ → ZMod m))
  apply hasPolychromColouring_fin_of_le (by simp)
  rw [polychromNumber_zmod hm_eq]
  exact le_polychromNumber h

/-- If gcd(d₁, d₂) = 1, at most one of d₁, d₂ is divisible by 3. -/
lemma gcd_not_both_div_three {d₁ d₂ : ℕ} (h : Nat.gcd d₁ d₂ = 1) :
    d₁ % 3 ≠ 0 ∨ d₂ % 3 ≠ 0 := by
  by_contra h'
  push_neg at h'
  obtain ⟨h1, h2⟩ := h'
  have : 3 ∣ Nat.gcd d₁ d₂ := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
  omega

/-- WLOG for Case 2: using zmod_set_swap, we can arrange that d₁ is not divisible by 3.
    Swapping (a, b) ↦ (-a, b-a) exchanges d₁ = gcd(b,m) and d₂ = gcd(b-a,m). -/
lemma main_case_two_wlog (m : ℕ) (a b : ℤ) (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  exact main_case_two m a b hm h_gcd_coprime h_min

/-- c - a + b > 0 when 0 < a < b ≤ c. -/
lemma c_sub_a_add_b_pos {a b c : ℤ} (ha : 0 < a) (hab : a < b) (hbc : a + b ≤ c) :
    0 < c - a + b := by
  linarith

/-- When (m : ℤ) = c - a + b with 0 < a < b and a + b ≤ c ≤ ... and c ≥ 289,
    we have m ≥ 289. -/
lemma m_ge_289 {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (hab : a < b) (hc : 289 ≤ c) :
    m ≥ 289 := by
  omega

/-- 2b - a < m when 0 < a, (m : ℤ) = c - a + b, and a + b ≤ c. -/
lemma two_b_sub_a_lt_m {a b c : ℤ} {m : ℕ}
    (hm : (m : ℤ) = c - a + b) (ha : 0 < a) (hbc : a + b ≤ c) :
    2 * b - a < ↑m := by
  omega

/--
The main theorem.
Combines the reduction to ZMod m with the case analysis on GCDs.
Uses: hasPolychromColouring_of_zmod_set, gcd_coprime_of_gcd_abc, zmod_set_card_eq_four,
      main_case_one (or main_case_two_wlog via zmod_set_swap), m_ge_289, c_sub_a_add_b_pos.
-/
theorem normal_bit :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → 289 ≤ c → Finset.gcd {a, b, c} id = 1 →
          HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hc hgcd
  set m := (c - a + b).toNat
  have hm_eq : (m : ℤ) = c - a + b :=
    Int.toNat_of_nonneg (le_of_lt (c_sub_a_add_b_pos ha hab hbc))
  have hm_pos : 0 < m := by omega
  have hm_ge : m ≥ 289 := m_ge_289 hm_eq hab hc
  have hcard := zmod_set_card_eq_four ha hab (two_b_sub_a_lt_m hm_eq ha hbc)
  have hcoprime := gcd_coprime_of_gcd_abc hm_eq hgcd
  apply hasPolychromColouring_of_zmod_set hm_eq
  set d₁ := Nat.gcd b.natAbs m
  set d₂ := Nat.gcd (b - a).natAbs m
  by_cases hmin : min d₁ d₂ = 1
  · apply main_case_one m a b hm_ge hcard
    have hd₁_pos : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    rcases min_choice d₁ d₂ with h | h <;> rw [h] at hmin <;> [left; right] <;> omega
  · have hd₁_pos : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    exact main_case_two_wlog m a b hm_ge hcoprime (by omega)
