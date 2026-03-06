import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Mathlib.Algebra.Ring.AddAut

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
    ext i; simp; tauto
  rw [this, polychromNumber_vadd]

/-- The set {0, b-a, b, 2b-a} is symmetric in the two repeated differences b and b-a:
    swapping them (replacing a by -a, b by b-a) gives the same set. -/
lemma zmod_set_swap (m : ℕ) (a b : ℤ) :
    zmod_set m (-a) (b - a) = zmod_set m a b := by
  simp only [zmod_set]
  grind

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
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  set bd := 4 * (m % 3) with hbd_def
  have hbd_le : bd ≤ m := by grind
  let c (p : ℕ) : ℕ :=
    if p < bd then (if p % 4 ≤ 1 then 0 else p % 4 - 1) else (p - bd) % 3
  have hc_lt3 : ∀ p, c p < 3 := by intro p; simp only [c]; split_ifs <;> lia
  have hc0 : c 0 = 0 := by simp only [c]; split_ifs <;> lia
  have hc_m1 : c (m - 1) = 2 := by simp only [c]; split_ifs <;> lia
  have hc_m2 : c (m - 2) = 1 := by simp only [c]; split_ifs <;> lia
  have hc_m3 : c (m - 3) = 0 := by simp only [c]; split_ifs <;> lia
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k => ?_⟩
  have hv : n.val < m := ZMod.val_lt n
  suffices ∃ a : ℕ, a ≤ 3 ∧ c ((n.val + a) % m) = k.val by
    obtain ⟨a, ha_le, hca⟩ := this
    have ha_lt_m : a < m := by grind
    refine ⟨(a : ZMod m), ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 from by grind with
        rfl | rfl | rfl | rfl <;> simp
    · ext
      change c (n + (a : ZMod m)).val = k.val
      have : (n + (a : ZMod m)).val = (n.val + a) % m := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt_m]
      rw [this, hca]
  set v := n.val with hv_def
  by_cases hwrap : v + 3 < m
  · have no_wrap : ∀ a, a ≤ 3 → (v + a) % m = v + a :=
      fun a ha => Nat.mod_eq_of_lt (by grind)
    by_cases hzone : v ≥ bd
    · set r := (v - bd) % 3
      have hr_lt : r < 3 := Nat.mod_lt _ (by grind)
      set a := (k.val + 3 - r) % 3
      have ha_lt : a < 3 := Nat.mod_lt _ (by grind)
      refine ⟨a, by grind, ?_⟩
      rw [no_wrap a (by grind)]
      show c (v + a) = k.val
      simp only [c]
      have : ¬ (v + a < bd) := by grind
      rw [if_neg this]
      change (v + a - bd) % 3 = k.val
      have := k.isLt; lia
    · push_neg at hzone
      by_cases hzone2 : v + 3 < bd
      · have h_in_bd : ∀ a, a ≤ 3 → v + a < bd := fun a ha => by grind
        set q := v % 4
        have find_a : ∀ kv : ℕ, kv < 3 → ∃ a, a ≤ 3 ∧ c (v + a) = kv := by
          intro kv hkv
          rcases show kv = 0 ∨ kv = 1 ∨ kv = 2 from by grind with rfl | rfl | rfl
          · refine ⟨(4 - q) % 4, by grind, ?_⟩
            have hmod : (v + (4 - q) % 4) % 4 = 0 := by grind
            simp only [c]
            rw [if_pos (h_in_bd _ (by grind)), if_pos (by grind)]
          · refine ⟨(6 - q) % 4, by grind, ?_⟩
            have hmod : (v + (6 - q) % 4) % 4 = 2 := by grind
            simp only [c]
            rw [if_pos (h_in_bd _ (by grind)), if_neg (by grind)]
            grind
          · refine ⟨(7 - q) % 4, by grind, ?_⟩
            have hmod : (v + (7 - q) % 4) % 4 = 3 := by grind
            simp only [c]
            rw [if_pos (h_in_bd _ (by grind)), if_neg (by grind)]
            grind
        obtain ⟨a, ha_le, ha_eq⟩ := find_a k.val k.isLt
        exact ⟨a, ha_le, by rw [no_wrap a ha_le]; exact ha_eq⟩
      · push_neg at hzone2
        have hbd_pos : 0 < bd := by grind
        have hc_boundary : ∀ j, j ≤ 5 → c (bd - 3 + j) = j % 3 := by
          intro j hj
          simp only [c]
          rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 from
            by grind with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> lia
        set j := v - (bd - 3)
        have hj_le : j ≤ 2 := by grind
        set a := (k.val + 3 - j % 3) % 3
        have ha_lt : a < 3 := Nat.mod_lt _ (by grind)
        refine ⟨a, by grind, ?_⟩
        rw [no_wrap a (by grind)]
        have hva : v + a = bd - 3 + (j + a) := by grind
        rw [hva, hc_boundary (j + a) (by grind)]
        rcases show j = 0 ∨ j = 1 ∨ j = 2 from by grind with h | h | h <;>
          fin_cases k <;> simp [a, h]
  · push_neg at hwrap
    have hmod_v : v % m = v := Nat.mod_eq_of_lt hv
    rcases show v = m - 3 ∨ v = m - 2 ∨ v = m - 1 from by grind
      with hveq | hveq | hveq
    · have h1 : (v + 1) % m = m - 2 := by
        have : v + 1 = m - 2 := by grind
        rw [this]; exact Nat.mod_eq_of_lt (by grind)
      have h2 : (v + 2) % m = m - 1 := by
        have : v + 2 = m - 1 := by grind
        rw [this]; exact Nat.mod_eq_of_lt (by grind)
      fin_cases k
      · exact ⟨0, by grind, by rw [add_zero, hmod_v, hveq]; exact hc_m3⟩
      · exact ⟨1, by grind, by rw [h1]; exact hc_m2⟩
      · exact ⟨2, by grind, by rw [h2]; exact hc_m1⟩
    · have h1 : (v + 1) % m = m - 1 := by
        have : v + 1 = m - 1 := by grind
        rw [this]; exact Nat.mod_eq_of_lt (by grind)
      have h2 : (v + 2) % m = 0 := by
        have : v + 2 = m := by grind
        rw [this, Nat.mod_self]
      fin_cases k
      · exact ⟨2, by grind, by rw [h2]; exact hc0⟩
      · exact ⟨0, by grind, by rw [add_zero, hmod_v, hveq]; exact hc_m2⟩
      · exact ⟨1, by grind, by rw [h1]; exact hc_m1⟩
    · have h1 : (v + 1) % m = 0 := by
        have : v + 1 = m := by grind
        rw [this, Nat.mod_self]
      have h2 : (v + 2) % m = 1 := by
        have : v + 2 = 1 + m := by grind
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by grind)]
      have h3 : (v + 3) % m = 2 := by
        have : v + 3 = 2 + m := by grind
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by grind)]
      fin_cases k
      · exact ⟨1, by grind, by rw [h1]; exact hc0⟩
      · by_cases hmod : m % 3 = 0
        · refine ⟨2, by grind, ?_⟩
          rw [h2]; change c 1 = 1
          simp only [c, hbd_def, hmod]; norm_num
        · refine ⟨3, by grind, ?_⟩
          rw [h3]; change c 2 = 1
          simp only [c]; split_ifs <;> lia
      · exact ⟨0, by grind, by rw [add_zero, hmod_v, hveq]; exact hc_m1⟩

/-- {0,1,3,4}: blocks 001212 (r=6), 0001212 (r+1=7). Frobenius bound: m > 29. -/
lemma table1_0134 (hm : m ≥ 30) :
    HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod m)) := by sorry

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
  · exact table1_0123 m (by grind)
  · exact table1_0134 m (by grind)
  · exact table1_0145 m (by grind)

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
  have key : polychromNumber (S.image (u.val * ·)) = polychromNumber S :=
    polychromNumber_iso (AddAut.mulLeft u)
  exact ⟨fun h => hasPolychromColouring_fin_of_le (by grind) (key ▸ le_polychromNumber h),
    fun h => hasPolychromColouring_fin_of_le (by grind) (key.symm ▸ le_polychromNumber h)⟩

-- Subcase (1c) per-residue lemmas: each reduces {0,1,g,g+1} to a Table 1 set
-- via multiplication by 3 (an automorphism of ZMod m when 3 ∤ m) and translation.

/-- m = 3g - 2: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,2,3,5}. -/
lemma case_one_res_3g_sub_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = 2 := by
    have : ((3 * g : ℕ) : ZMod m) = (m + 2 : ℕ) := by congr 1; grind
    simpa using this
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 5 := by grind
  simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g_mod, image_singleton,
    h3g1_mod, insert_comm] using table1_0235 m (by grind)

/-- m = 3g - 1: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,1,3,4}. -/
lemma case_one_res_3g_sub_1 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = 1 := by
    have : ((3 * g : ℕ) : ZMod m) = (m + 1 : ℕ) := by congr 1; grind
    simpa using this
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 4 := by grind
  simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g_mod,
    image_singleton, h3g1_mod, insert_comm] using table1_0134 m (by grind)

/-- m = 3g + 1: ×3 maps {0,1,g,g+1} to {0,3,-1,2}, a translate of {0,1,3,4}. -/
lemma case_one_res_3g_add_1 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -1 := by
    have : ((3 * g + 1 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 2 := by grind
  have : {0, (3 : ZMod m), -1, 2} = (-1 : ZMod m) +ᵥ ({0, 1, 3, 4} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0134 m (by grind)

/-- m = 3g + 2: ×3 maps {0,1,g,g+1} to {0,3,-2,1}, a translate of {0,2,3,5}. -/
lemma case_one_res_3g_add_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -2 := by
    have : ((3 * g + 2 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 1 := by grind
  have : {0, (3 : ZMod m), -2, 1} = (-2 : ZMod m) +ᵥ ({0, 2, 3, 5} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0235 m (by grind)

/-- m = 3g + 4: ×3 maps {0,1,g,g+1} to {0,3,-4,-1}, a translate of {0,3,4,7}. -/
lemma case_one_res_3g_add_4 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 4) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -4 := by
    have : ((3 * g + 4 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = -1 := by grind
  have : {0, (3 : ZMod m), -4, -1} = (-4 : ZMod m) +ᵥ ({0, 3, 4, 7} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0347 m (by grind)

/-- m = 3g + 5: ×3 maps {0,1,g,g+1} to {0,3,-5,-2}, a translate of {0,3,5,8}. -/
lemma case_one_res_3g_add_5 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 5) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -5 := by
    have : ((3 * g + 5 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = -2 := by grind
  have : {0, (3 : ZMod m), -5, -2} = (-5 : ZMod m) +ᵥ ({0, 3, 5, 8} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0358 m (by grind)

/-- Subcase (1c) assembled: dispatches to the six per-residue lemmas above. -/
lemma case_one_residues (g : ℕ) (hm : m ≥ 289) (h_res : m % 3 ≠ 0)
    (h_range : 2 * (m / 6) ≤ g ∧ g ≤ (m + 2) / 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨hl, hr⟩ := h_range
  have h1 : m = 3 * g - 2 ∨ m = 3 * g - 1 ∨ m = 3 * g + 1 ∨
      m = 3 * g + 2 ∨ m = 3 * g + 4 ∨ m = 3 * g + 5 := by grind
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact case_one_res_3g_sub_2 _ g hm rfl
  · exact case_one_res_3g_sub_1 _ g hm rfl
  · exact case_one_res_3g_add_1 _ g hm rfl
  · exact case_one_res_3g_add_2 _ g hm rfl
  · exact case_one_res_3g_add_4 _ g hm rfl
  · exact case_one_res_3g_add_5 _ g hm rfl

-- Subcase (1d) sub-subcases, split by g mod 3.

/-- (1d), g ≢ 0 (mod 3): the periodic coloring 012012...012 works because
    each translate of {0,1,g,g+1} hits all 3 residue classes mod 3. -/
lemma case_one_div_g_not_three (g : ℕ)
    (h_div : m = 3 * g ∨ m = 3 * g + 3)
    (hg3 : g % 3 ≠ 0) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  have h3_dvd : 3 ∣ m := by rcases h_div with rfl | rfl <;> grind
  haveI : NeZero m := ⟨by grind⟩
  apply HasPolychromColouring.of_image (ZMod.castHom h3_dvd (ZMod 3))
  simp only [Finset.image_insert, Finset.image_singleton,
    map_zero, map_one, map_add, map_natCast]
  have hg12 : g % 3 = 1 ∨ g % 3 = 2 := by grind
  suffices ({0, 1, (g : ZMod 3), (g : ZMod 3) + 1} :
      Finset (ZMod 3)) = Finset.univ by
    rw [this]; exact hasPolychromColouring_univ
  rcases hg12 with h | h <;> {
    have : (g : ZMod 3) = ↑(g % 3 : ℕ) := by
      rw [ZMod.natCast_mod]
    simp only [this, h]; decide
  }

private lemma color_shift_r (r q : ℕ) :
    ((r + 1) % 3 + (3 - q % 3)) % 3 =
      ((r % 3 + (3 - q % 3)) % 3 + 1) % 3 := by
  have : q % 3 < 3 := Nat.mod_lt q (by grind)
  rcases show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by grind with h | h | h <;>
    simp only [h, Nat.add_mod, Nat.mod_self, Nat.mod_mod] <;> grind

private lemma color_shift_q (r q : ℕ) :
    (r % 3 + (3 - (q + 1) % 3)) % 3 =
      ((r % 3 + (3 - q % 3)) % 3 + 2) % 3 := by
  have : q % 3 < 3 := Nat.mod_lt q (by grind)
  rcases show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by grind with h | h | h <;>
    simp only [h, Nat.add_mod, Nat.mod_self, Nat.mod_mod] <;> grind

private lemma nat_mod_div {a b q r : ℕ} (hb : 0 < b) (heq : a = b * q + r)
    (hr : r < b) : a % b = r ∧ a / b = q := by
  subst heq
  exact ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr],
         by rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, add_zero]⟩

private lemma mod3_witness {s k : ℕ} (hs : s < 3) (hk : k < 3) :
    ((k + 3 - s) % 3 = 0 → s = k) ∧
    ((k + 3 - s) % 3 = 1 → (s + 1) % 3 = k) ∧
    ((k + 3 - s) % 3 = 2 → (s + 2) % 3 = k) := by grind

private lemma endgame_witness {g : ℕ} {c : ℕ → ℕ}
    {v s : ℕ} {k : Fin 3} (hs : s < 3)
    (a₀ a₁ a₂ : ℕ)
    (ha₀ : a₀ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (ha₁ : a₁ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (ha₂ : a₂ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (hc₀ : c (v + a₀) = s)
    (hc₁ : c (v + a₁) = (s + 1) % 3)
    (hc₂ : c (v + a₂) = (s + 2) % 3) :
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      c (v + a) = k.val := by
  have hk := k.isLt
  have wit := mod3_witness hs hk
  set d := (k.val + 3 - s) % 3
  rcases show d = 0 ∨ d = 1 ∨ d = 2 from by grind
    with hd | hd | hd
  · exact ⟨a₀, ha₀, by rw [hc₀]; exact wit.1 hd⟩
  · exact ⟨a₁, ha₁, by rw [hc₁]; exact wit.2.1 hd⟩
  · exact ⟨a₂, ha₂, by rw [hc₂]; exact wit.2.2 hd⟩

/-- Lift a ℕ-level coloring witness for {0,1,g,g+1} to ZMod m. -/
private lemma lift_coloring_witness {m g : ℕ} [NeZero m] [Fact (1 < m)]
    (hg_lt : g + 1 < m) {c : ℕ → ℕ} (hc_lt : ∀ p, c p < 3)
    (hc_period : ∀ p, c (p % m) = c p)
    {n : ZMod m} {k : Fin 3}
    (h : ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (n.val + a) = k.val) :
    ∃ s ∈ ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)),
      (⟨c (n + s).val, hc_lt _⟩ : Fin 3) = k := by
  obtain ⟨a, ha, hca⟩ := h
  have ha_lt : a < m := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> grind
  exact ⟨(a : ZMod m),
    by simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
       rcases ha with rfl | rfl | rfl | rfl <;> simp,
    by ext; change c (n + (a : ZMod m)).val = k.val
       rw [show (n + (a : ZMod m)).val = (n.val + a) % m from by
         rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt], hc_period, hca]⟩

lemma case_one_div_3g (g : ℕ) (hm_eq : m = 3 * g)
    (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  let c (p : ℕ) : ℕ := (p % 3 + p / g) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c, hm_eq]
    have h1 : p % (3 * g) % 3 = p % 3 := Nat.mod_mod_of_dvd p (dvd_mul_right 3 g)
    have h2 : p / g = p % (3 * g) / g + 3 * (p / (3 * g)) := by
      conv_lhs => rw [show p = p % (3 * g) + (3 * (p / (3 * g))) * g from by
        rw [show (3 * (p / (3 * g))) * g = 3 * g * (p / (3 * g)) from by ring]
        exact (Nat.mod_add_div p (3 * g)).symm]
      exact Nat.add_mul_div_right _ _ hg
    rw [h1, h2]; grind
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val
  set r := v % g with hr_def
  set q := v / g with hq_def
  have hv_eq : v = g * q + r := (Nat.div_add_mod v g).symm
  have hr_lt : r < g := Nat.mod_lt _ hg
  have gk_mod3 : ∀ k a, (g * k + a) % 3 = a % 3 := by
    intro k a; rw [ht, show 3 * t * k + a = 3 * (t * k) + a from by ring, Nat.mul_add_mod]
  have gk_mul_mod3 : ∀ k, (g * k) % 3 = 0 := fun k => by simpa using gk_mod3 k 0
  have color_at : ∀ q' r', r' < g → c (g * q' + r') = (r' % 3 + q') % 3 := by
    intro q' r' hr'
    simp only [c, gk_mod3, Nat.mul_add_div hg, Nat.div_eq_of_lt hr', add_zero]
  by_cases hr_lt_gm1 : r + 1 < g
  · have hcv : c v = (r % 3 + q) % 3 := hv_eq ▸ color_at q r hr_lt
    have hcvg : c (v + g) = (r % 3 + (q + 1)) % 3 := by
      rw [show v + g = g * (q + 1) + r from by rw [mul_add, mul_one]; grind]
      exact color_at (q + 1) r hr_lt
    have hcvg1 : c (v + g + 1) = ((r + 1) % 3 + (q + 1)) % 3 := by
      rw [show v + g + 1 = g * (q + 1) + (r + 1) from by rw [mul_add, mul_one]; grind]
      exact color_at (q + 1) (r + 1) (by grind)
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g (g + 1)
      (by simp) (by simp) (by simp)
      hcv (by rw [hcvg]; grind) (show c (v + g + 1) = _ by rw [hcvg1]; grind)
  · push_neg at hr_lt_gm1
    have hr_eq : r = g - 1 := by grind
    have ht_pos : 0 < t := by grind
    have hcv : c v = (2 + q) % 3 := by
      rw [show v = g * q + r from hv_eq, color_at q r hr_lt, hr_eq, ht]; grind
    have hcv1 : c (v + 1) = (q + 1) % 3 := by
      rw [show v + 1 = g * (q + 1) + 0 from by rw [mul_add, mul_one]; grind,
          color_at (q + 1) 0 hg]; simp
    have hcvg : c (v + g) = (2 + (q + 1)) % 3 := by
      rw [show v + g = g * (q + 1) + (g - 1) from by rw [mul_add, mul_one]; grind,
          color_at (q + 1) (g - 1) (by grind), ht]; grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by rw [hcvg]; grind) (by rw [hcv1]; grind)

lemma case_one_div_3g3 (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  set h := g + 1 with hh_def
  have hh_pos : 0 < h := by grind
  have hh_m : m = 3 * h := by grind
  let c (p : ℕ) : ℕ := (p % h % 3 + (3 - p / h % 3)) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c, hh_m]
    set Q := p / (3 * h)
    set R := p % (3 * h) with hR_def
    conv_rhs => rw [show p = h * (3 * Q) + R from by
      rw [show h * (3 * Q) = 3 * h * Q from by ring]; exact (Nat.div_add_mod p (3 * h)).symm]
    have hmod : (h * (3 * Q) + R) % h = R % h := Nat.mul_add_mod h _ R
    have hdiv : (h * (3 * Q) + R) / h % 3 = R / h % 3 := by
      rw [show h * (3 * Q) + R = R + h * (3 * Q) from by ring,
          Nat.add_mul_div_left _ _ hh_pos]; grind
    rw [hmod, hdiv]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val
  set r := v % h with hr_def
  set q := v / h with hq_def
  have hv_eq : v = h * q + r := (Nat.div_add_mod v h).symm
  have hr_lt : r < h := Nat.mod_lt _ hh_pos
  have color_at : ∀ q' r', r' < h → c (h * q' + r') = (r' % 3 + (3 - q' % 3)) % 3 := by
    intro q' r' hr'
    change ((h * q' + r') % h % 3 + (3 - (h * q' + r') / h % 3)) % 3 = _
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr',
        Nat.mul_add_div hh_pos, Nat.div_eq_of_lt hr', add_zero]
  by_cases hrg : r = g
  · have hcv : c v = (3 - q % 3) % 3 := by
      rw [show v = h * q + r from hv_eq, color_at q r hr_lt, hrg, ht, Nat.mul_mod_right]
      grind
    have hcv1 : c (v + 1) = (3 - (q + 1) % 3) % 3 := by
      rw [show v + 1 = h * (q + 1) + 0 from by rw [mul_add, mul_one]; grind,
          color_at (q + 1) 0 (by grind)]
      grind
    have hcvg : c (v + g) = (2 + (3 - (q + 1) % 3)) % 3 := by
      rw [show v + g = h * (q + 1) + (g - 1) from by rw [mul_add, mul_one]; grind,
          color_at (q + 1) (g - 1) (by grind), ht,
          show 3 * t - 1 = 3 * (t - 1) + 2 from by grind]; simp
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by rw [hcvg]; grind) (by rw [hcv1]; grind)
  · have hcv : c v = (r % 3 + (3 - q % 3)) % 3 := rfl
    have hcv1 : c (v + 1) = ((r + 1) % 3 + (3 - q % 3)) % 3 := by
      rw [show v + 1 = h * q + (r + 1) from by grind, color_at q (r + 1) (by grind)]
    have hcvg1 : c (v + g + 1) = (r % 3 + (3 - (q + 1) % 3)) % 3 := by
      rw [show v + g + 1 = h * (q + 1) + r from by rw [mul_add, mul_one]; grind,
          color_at (q + 1) r hr_lt]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 1 (g + 1)
      (by simp) (by simp) (by simp)
      hcv (by rw [hcv1]; exact color_shift_r r q)
      (show c (v + g + 1) = _ by rw [hcvg1]; exact color_shift_q r q)

/-- Subcase (1d) assembled: dispatches to the three sub-subcases above. -/
lemma case_one_divisible (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  by_cases hg3 : g % 3 = 0
  · rcases h_div with h | h
    · exact case_one_div_3g m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
    · exact case_one_div_3g3 m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
  · exact case_one_div_g_not_three m g h_div hg3

/-- Subcase (1b) with s=3: interval coloring for g > ⌈m/3⌉.
    Same argument as case_one_interval but with 3 intervals of size ≈ m/3. -/
lemma case_one_interval_large (g : ℕ) (h_ge : (m + 2) / 3 < g)
    (h_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  sorry

/-- Combined dispatch: applies subcases (1a)–(1d) for 2 ≤ g ≤ m/2 and m ≥ 289. -/
lemma case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g)
    (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  by_cases hg4 : g ≤ 4
  · exact case_one_small_g m g hm (by simp; grind)
  · push_neg at hg4
    by_cases hg_int : g < 2 * (m / 6)
    · exact case_one_interval m g (by grind) hg_int
    · push_neg at hg_int
      by_cases hg_res : g ≤ (m + 2) / 3
      · by_cases h3 : m % 3 = 0
        · exact case_one_divisible m g hm (by grind)
        · exact case_one_residues m g hm h3 ⟨hg_int, hg_res⟩
      · push_neg at hg_res
        exact case_one_interval_large m g hg_res hg_le

/-- WLOG g ≤ m/2: in ZMod m, {0,1,m-g,m-g+1} = (-g) +ᵥ {0,1,g,g+1},
    so HasPolychromColouring is preserved. -/
lemma case_one_complement (g : ℕ) (hg : g < m) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (↑(m - g) : ZMod m), (↑(m - g) : ZMod m) + 1} : Finset (ZMod m)) ↔
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have key : (↑(m - g) : ZMod m) = -(↑g : ZMod m) := by
    rw [Nat.cast_sub hg.le, ZMod.natCast_self, zero_sub]
  rw [key, show ({0, 1, -(↑g : ZMod m), -(↑g : ZMod m) + 1} : Finset (ZMod m)) =
      (-(↑g : ZMod m)) +ᵥ ({0, 1, (↑g : ZMod m), (↑g : ZMod m) + 1} : Finset (ZMod m)) from by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add, neg_add_cancel]
    grind]
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
  have hm4 : 4 ≤ m := by
    haveI : NeZero m := ⟨by grind⟩
    calc 4 = (zmod_set m a b).card := hcard.symm
      _ ≤ Fintype.card (ZMod m) := Finset.card_le_univ _
      _ = m := ZMod.card m
  haveI : NeZero m := ⟨by grind⟩
  have hub : IsUnit ((b : ℤ) : ZMod m) := isUnit_intCast_of_natAbs_coprime hd
  set bz : ZMod m := (b : ZMod m)
  set az : ZMod m := (a : ZMod m)
  set g' : ZMod m := bz⁻¹ * (bz - az)
  have hbg' : bz * g' = bz - az := by
    change bz * (bz⁻¹ * (bz - az)) = bz - az
    rw [← mul_assoc, ZMod.mul_inv_of_unit _ hub, one_mul]
  have hbg'1 : bz * (g' + 1) = 2 * bz - az := by
    rw [mul_add, mul_one, hbg']; ring
  have hset : zmod_set m a b =
      ({0, 1, g', g' + 1} : Finset (ZMod m)).image (bz * ·) := by
    simp only [zmod_set, Finset.image_insert, Finset.image_singleton]
    simp only [mul_zero, mul_one, hbg', hbg'1]
    push_cast
    grind
  have hval : (g'.val : ZMod m) = g' := ZMod.natCast_zmod_val g'
  have hinj : Function.Injective (bz * · : ZMod m → ZMod m) := by
    intro x y (hxy : bz * x = bz * y)
    have h1 : bz⁻¹ * (bz * x) = bz⁻¹ * (bz * y) := congr_arg (bz⁻¹ * ·) hxy
    simp only [← mul_assoc, ZMod.inv_mul_of_unit _ hub, one_mul] at h1
    exact h1
  have hcard4 : ({0, 1, g', g' + 1} : Finset (ZMod m)).card = 4 := by
    rwa [hset, Finset.card_image_of_injective _ hinj] at hcard
  refine ⟨g'.val, ?_, ?_, ?_⟩
  · by_contra hlt; push_neg at hlt
    have hcases : g'.val = 0 ∨ g'.val = 1 := by grind
    rcases hcases with h | h
    · have hg'0 : g' = 0 := by rw [← hval, h, Nat.cast_zero]
      have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1} := by
        rw [hg'0, zero_add]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]
      linarith [Finset.card_le_card hsub, Finset.card_le_two (a := (0 : ZMod m)) (b := 1)]
    · have hg'1 : g' = 1 := by rw [← hval, h, Nat.cast_one]
      have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, (1 : ZMod m) + 1} := by
        rw [hg'1]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]
      linarith [Finset.card_le_card hsub,
        Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := (1 : ZMod m) + 1)]
  · by_contra hgt; push_neg at hgt
    have hval_lt := ZMod.val_lt g'
    have hgm1 : g'.val = m - 1 := by grind
    have hg'p1 : g' + 1 = 0 := by
      rw [← hval, hgm1, Nat.cast_sub (by grind), Nat.cast_one, ZMod.natCast_self, zero_sub,
        neg_add_cancel]
    have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, g'} := by
      rw [hg'p1]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
    linarith [Finset.card_le_card hsub,
      Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := g')]
  · conv at hset => rhs; rw [show g' = (g'.val : ZMod m) from hval.symm]
    exact hset

/-- Aggregation of Main Case 1.
    Reduces to {0,1,g,g+1} via exists_g_of_coprime and hasPolychromColouring_mul_unit,
    applies WLOG g ≤ m/2 via case_one_complement,
    then dispatches via case_one_dispatch. -/
lemma main_case_one (a b : ℤ) (hm : m ≥ 289)
    (hcard : (zmod_set m a b).card = 4)
    (h_gcd : Nat.gcd b.natAbs m = 1 ∨ Nat.gcd (b - a).natAbs m = 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  suffices ∀ a' b' : ℤ, Nat.gcd b'.natAbs m = 1 →
      (zmod_set m a' b').card = 4 →
      HasPolychromColouring (Fin 3) (zmod_set m a' b') by
    rcases h_gcd with hb | hba
    · exact this a b hb hcard
    · rw [← zmod_set_swap m a b]
      apply this (-a) (b - a) hba
      rwa [zmod_set_swap]
  intro a' b' hd hcard'
  obtain ⟨g, hg_ge, hg_le, hset⟩ := exists_g_of_coprime m a' b' hd (by grind) hcard'
  obtain ⟨u, hu⟩ := isUnit_intCast_of_natAbs_coprime hd
  rw [hset, ← hu]
  rw [hasPolychromColouring_mul_unit]
  by_cases hg_half : g ≤ m / 2
  · exact case_one_dispatch m g hm hg_ge hg_half
  · push_neg at hg_half
    rw [← case_one_complement m g (by grind)]
    exact case_one_dispatch m (m - g) hm (by grind) (by grind)

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
  set d₁ := Nat.gcd b.natAbs m with hd₁_def
  set e₁ := m / d₁ with he₁_def
  have hd₁_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
  have hd₁_pos : 0 < d₁ := Nat.pos_of_ne_zero (by intro h; simp [h] at h_min)
  have he₁_pos : 0 < e₁ := Nat.div_pos (Nat.le_of_dvd (by omega) hd₁_dvd) hd₁_pos
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd₁_dvd).symm
  have he₁_ge2 : e₁ ≥ 2 := by obtain ⟨k, hk⟩ := he1_even; omega
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  -- d₁ divides b (ℤ level)
  have hd₁_dvd_b : (d₁ : ℤ) ∣ b := by
    have := Int.gcd_dvd_left b (m : ℤ)
    simp only [Int.gcd, Int.natAbs_cast] at this; exact this
  -- b ≡ 0 mod d₁
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd₁_dvd_b
  -- (b-a) is a unit in ZMod d₁
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (by rwa [Nat.gcd_comm] at h_gcd_coprime)
  -- b/d₁ is coprime to e₁
  obtain ⟨q, hq⟩ := hd₁_dvd_b
  have hq_cop : Nat.Coprime q.natAbs e₁ := by
    have hbn : b.natAbs = d₁ * q.natAbs := by
      rw [hq, Int.natAbs_mul, Int.natAbs_cast]
    have hq_eq : q.natAbs = b.natAbs / d₁ := Nat.eq_div_of_eq_mul_left hd₁_pos hbn
    rw [hq_eq]; exact Nat.coprime_div_gcd_div_gcd hd₁_pos
  -- e₁ * b ≡ 0 mod m
  have he₁b_zero : (e₁ : ZMod m) * (Int.cast b : ZMod m) = 0 := by
    rw [hq]; push_cast
    rw [show (e₁ : ZMod m) * ((d₁ : ZMod m) * (q : ZMod m)) =
      ((e₁ * d₁ : ℕ) : ZMod m) * (q : ZMod m) from by push_cast; ring]
    rw [show (e₁ * d₁ : ℕ) = m from by omega]
    simp [ZMod.natCast_self]
  -- Key lemma: congruence mod e₁ is invisible after ×b in ZMod m
  have hmod_b : ∀ n₁ n₂ : ℤ, (e₁ : ℤ) ∣ (n₁ - n₂) →
      (↑n₁ : ZMod m) * ↑b = (↑n₂ : ZMod m) * ↑b := by
    intro n₁ n₂ ⟨k, hk⟩
    suffices ((n₁ - n₂ : ℤ) : ZMod m) * ↑b = 0 by
      rwa [Int.cast_sub, sub_mul, sub_eq_zero] at this
    rw [hk]; push_cast
    rw [show (↑e₁ * k : ZMod m) * ↑b = k * ((e₁ : ZMod m) * ↑b) from by ring,
      he₁b_zero, mul_zero]
  -- Define the cycle map φ : ZMod d₁ × ZMod e₁ → ZMod m
  let φ : ZMod d₁ × ZMod e₁ → ZMod m :=
    fun ⟨i, j⟩ => (i.val : ZMod m) * ↑(b - a) + (j.val : ZMod m) * ↑b
  -- φ(i, j+1) = φ(i, j) + b
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; simp only [φ]
    suffices ((j + 1).val : ZMod m) * (↑b : ZMod m) =
        (j.val : ZMod m) * ↑b + ↑b by
      rw [this]; ring
    rw [show (j.val : ZMod m) * ↑b + ↑b = ((j.val : ℤ) + 1 : ZMod m) * ↑b from by
      push_cast; ring]
    exact hmod_b ((j + 1).val : ℤ) ((j.val : ℤ) + 1) ⟨-↑((j.val + 1) / e₁), by
      have hval : (j + 1).val = (j.val + 1) % e₁ := by
        rw [ZMod.val_add]; congr 1; simp [ZMod.val_one]; omega
      have := Nat.div_add_mod (j.val + 1) e₁
      rw [hval]; push_cast; omega⟩
  -- Cycle index function α : ZMod m → ZMod d₁
  obtain ⟨u_ba, hu_ba⟩ := hba_unit
  let α : ZMod m → ZMod d₁ :=
    fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
  -- α(x + b) = α(x)
  have hα_b : ∀ x, α (x + ↑b) = α x := by
    intro x; simp only [α, map_add, map_intCast, hb_zero, add_zero]
  -- α(x + (b-a)) = α(x) + 1
  have hα_ba : ∀ x, α (x + ↑(b - a)) = α x + 1 := by
    intro x; simp only [α, map_add, map_intCast, add_mul]
    rw [hu_ba]; ring_nf; rw [u_ba.mul_inv]; ring
  -- α(φ(i, j)) = i
  have hα_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (φ (i, j)) = i := by
    intro i j; simp only [α, φ]
    rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast, map_intCast,
      hb_zero, mul_zero, add_zero, mul_assoc]
    rw [hu_ba]; rw [u_ba.mul_inv]; rw [mul_one, ZMod.natCast_val]
  -- φ is injective
  have hφ_inj : Function.Injective φ := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    have hi : i₁ = i₂ := by
      have h1 := hα_φ i₁ j₁; have h2 := hα_φ i₂ j₂
      rw [h] at h1; rw [← h1, ← h2]
    subst hi; congr 1
    -- From h: j₁.val * b = j₂.val * b in ZMod m
    have hj_eq : (↑j₁.val : ZMod m) * ↑b = (↑j₂.val : ZMod m) * ↑b :=
      add_left_cancel (show (↑i₁.val : ZMod m) * ↑(b - a) + _ = _ + _ from h)
    -- Convert to ℤ divisibility: m | (j₁.val - j₂.val) * b
    have h_dvd : (m : ℤ) ∣ ((j₁.val : ℤ) - j₂.val) * b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have : ((j₁.val : ZMod m) - (j₂.val : ZMod m)) * (↑b : ZMod m) = 0 := by
        rw [sub_mul]; exact sub_eq_zero.mpr hj_eq
      convert this using 1; push_cast; ring
    -- Factor b = d₁ * q, cancel d₁
    have h_dvd2 : (e₁ : ℤ) ∣ ((j₁.val : ℤ) - j₂.val) * q := by
      rw [hq] at h_dvd
      have : (d₁ : ℤ) * (e₁ : ℤ) ∣ (d₁ : ℤ) * (((j₁.val : ℤ) - j₂.val) * q) := by
        convert h_dvd using 1 <;> [push_cast; omega; ring]
      exact (mul_dvd_mul_iff_left (by positivity : (d₁ : ℤ) ≠ 0)).mp this
    -- Use coprimality at ℕ level via natAbs
    have h_nat : e₁ ∣ ((j₁.val : ℤ) - j₂.val).natAbs := by
      have h1 : e₁ ∣ (((j₁.val : ℤ) - j₂.val) * q).natAbs := by
        rwa [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
      rw [Int.natAbs_mul] at h1
      exact hq_cop.symm.dvd_of_dvd_mul_right h1
    have h_bound : ((j₁.val : ℤ) - j₂.val).natAbs < e₁ := by
      rcases le_or_lt (j₁.val : ℤ) j₂.val with h | h
      · rw [Int.natAbs_of_nonpos (by omega)]; exact by omega
      · rw [Int.natAbs_of_nonneg (by omega)]; exact by omega
    have h_zero := Nat.eq_zero_of_dvd_of_lt h_nat h_bound
    have h_eq : j₁.val = j₂.val := by
      rwa [Int.natAbs_eq_zero, sub_eq_zero, Nat.cast_inj] at h_zero
    exact ZMod.val_injective h_eq
  -- φ is bijective
  have hφ_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr
      ⟨hφ_inj, by simp [Fintype.card_prod, ZMod.card, hm_eq]⟩
  let Φ := Equiv.ofBijective φ hφ_bij
  -- Φ.symm(x+b) = (same_i, j+1)
  have hΦ_add_b : ∀ x : ZMod m,
      (Φ.symm (x + ↑b)).1 = (Φ.symm x).1 ∧
      (Φ.symm (x + ↑b)).2 = (Φ.symm x).2 + 1 := by
    intro x
    have key := hφ_add_b (Φ.symm x).1 (Φ.symm x).2
    rw [Equiv.apply_symm_apply] at key
    have hsym := congr_arg Φ.symm key.symm
    simp only [Equiv.symm_apply_apply] at hsym
    exact ⟨(Prod.ext_iff.mp hsym).1.symm, (Prod.ext_iff.mp hsym).2.symm⟩
  -- (Φ.symm x).1 = α x
  have hΦ_cycle : ∀ x : ZMod m, (Φ.symm x).1 = α x := by
    intro x
    have := hα_φ (Φ.symm x).1 (Φ.symm x).2
    rwa [Equiv.apply_symm_apply] at this
  -- Color table: last odd cycle uses {1,2}, even cycles use {0,1}, odd non-last use {0,2}
  have hd₁_ge2 : d₁ ≥ 2 := by
    have := Nat.min_le_left (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m)
    omega
  let f : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
    if i.val = d₁ - 1 ∧ ¬Even d₁ then ⟨1 + j.val % 2, by omega⟩
    else if i.val % 2 = 0 then ⟨j.val % 2, by omega⟩
    else ⟨2 * (j.val % 2), by omega⟩
  -- Parity flips: j.val % 2 ≠ (j+1).val % 2
  have hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2 := by
    intro j
    have hval : (j + 1).val = (j.val + 1) % e₁ := by
      rw [ZMod.val_add]; congr 1; simp; omega
    rw [hval]
    obtain ⟨k, hk⟩ := he1_even
    omega
  -- f(i,j) ≠ f(i,j+1)
  have hf_alt : ∀ i : ZMod d₁, ∀ j : ZMod e₁, f (i, j) ≠ f (i, j + 1) := by
    intro i j; simp only [f]
    have := hparity j
    split_ifs <;> simp [Fin.ext_iff] <;> omega
  -- Coverage: adjacent cycles cover all 3 colors
  have hf_covers : ∀ i : ZMod d₁, ∀ j₁ j₂ : ZMod e₁, ∀ k : Fin 3,
      k = f (i, j₁) ∨ k = f (i, j₁ + 1) ∨
      k = f (i + 1, j₂) ∨ k = f (i + 1, j₂ + 1) := by
    intro i j₁ j₂ k
    simp only [f]
    have h1 := hparity j₁; have h2 := hparity j₂
    have hi_bound := i.val_lt (n := d₁)
    have hi1_val : (i + 1).val = if i.val + 1 < d₁ then i.val + 1 else 0 := by
      have hival : (i + 1).val = (i.val + 1) % d₁ := by
        rw [ZMod.val_add]; congr 1; simp; omega
      rw [hival]; split_ifs with h <;> omega
    split_ifs <;> fin_cases k <;> simp_all [Fin.ext_iff] <;> omega
  -- Define coloring and prove polychromaticity
  let χ : ZMod m → Fin 3 := f ∘ Φ.symm
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set p := Φ.symm n; set i := p.1; set j := p.2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := by
    simp only [χ, Function.comp]
    obtain ⟨h1, h2⟩ := hΦ_add_b n
    exact congr_arg f (Prod.ext h1 h2)
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') := by
    simp only [χ, Function.comp]
    exact congr_arg f (Prod.ext (by rw [hΦ_cycle, hα_ba, hΦ_cycle]) rfl)
  have hχ_n2ba : χ (n + ↑(2 * b - a)) = f (i + 1, j' + 1) := by
    simp only [χ, Function.comp]
    have h2ba : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by push_cast; ring
    rw [h2ba]; obtain ⟨h1, h2⟩ := hΦ_add_b (n + ↑(b - a))
    exact congr_arg f (Prod.ext (by rw [h1, hΦ_cycle, hα_ba, hΦ_cycle]) h2)
  rcases hf_covers i j j' k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  · exact ⟨↑b, by simp, by rw [hχ_nb, h]⟩
  · exact ⟨↑(b - a), by simp, by rw [hχ_nba, h]⟩
  · exact ⟨↑(2 * b - a), by simp, by rw [hχ_n2ba, h]⟩

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
          obtain ⟨k, hk⟩ := ho; grind
        exact case_two_odd_large m a b hm h_gcd_coprime h_min hd ho this

end Case2_MultipleCycles

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
  have ne01 := hne 0 (b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne02 := hne 0 b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne03 := hne 0 (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne12 := hne (b - a) b (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne13 := hne (b - a) (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
  have ne23 := hne b (2 * b - a) (by grind) (by grind) (by grind) (by grind) (by grind)
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
  change HasPolychromColouring (Fin 3)
    (({0, a, b, c} : Finset ℤ).image (Int.cast : ℤ → ZMod m))
  apply hasPolychromColouring_fin_of_le (by simp)
  rw [polychromNumber_zmod hm_eq]
  exact le_polychromNumber h

/-- The main theorem: combines the reduction to ZMod m with the case analysis on GCDs. -/
theorem normal_bit :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → 289 ≤ c → Finset.gcd {a, b, c} id = 1 →
          HasPolychromColouring (Fin 3) {0, a, b, c} := by
  intro a b c ha hab hbc hc hgcd
  set m := (c - a + b).toNat
  have hm_eq : (m : ℤ) = c - a + b := Int.toNat_of_nonneg (by linarith)
  have hm_pos : 0 < m := by grind
  have hcard := zmod_set_card_eq_four ha hab (by linarith)
  apply hasPolychromColouring_of_zmod_set hm_eq
  set d₁ := Nat.gcd b.natAbs m
  set d₂ := Nat.gcd (b - a).natAbs m
  by_cases hmin : min d₁ d₂ = 1
  · apply main_case_one m a b (by grind) hcard
    have hd₁_pos : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have hd₂_pos : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    rcases min_choice d₁ d₂ with h | h <;> rw [h] at hmin <;> [left; right] <;> grind
  · have : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm_pos
    have : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hm_pos
    exact main_case_two m a b (by grind) (gcd_coprime_of_gcd_abc hm_eq hgcd) (by grind)
