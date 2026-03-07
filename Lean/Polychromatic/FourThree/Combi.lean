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
  sorry /- TEMPORARILY SORRIED for faster iteration
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
-/

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

/-! ### Case (2d): d₁, e₁ both odd, e₁ ≥ 19

The base pattern on C₀ uses three alternating bicolor intervals of sizes u, v, w.
Each subsequent cycle is a rotation of C₀. The rotation amount must be in [u, e₁-u].
-/

/-- Partition parameter: first interval size for case 2d.
    u = e₁/3 + e₁%3 (i.e. k+r where e₁ = 3k+r).
    For e₁ odd: r=0 → u=k (odd), r=1 → u=k+1 (odd), r=2 → u=k+2 (odd). -/
private def case2d_u (e₁ : ℕ) : ℕ := e₁ / 3 + e₁ % 3

/-- Second interval size for case 2d.
    v = e₁/3 + (1 if e₁%3 = 1 else 0).
    r=0: v = k   r=1: v = k+1   r=2: v = k -/
private def case2d_v (e₁ : ℕ) : ℕ :=
  if e₁ % 3 = 1 then e₁ / 3 + 1 else e₁ / 3

private lemma case2d_u_odd {e₁ : ℕ} (he : Odd e₁) : Odd (case2d_u e₁) := by
  simp only [case2d_u]; obtain ⟨k, hk⟩ := he; rw [hk, Nat.odd_iff]; omega

private lemma case2d_v_odd {e₁ : ℕ} (he : Odd e₁) : Odd (case2d_v e₁) := by
  simp only [case2d_v]; obtain ⟨k, hk⟩ := he; rw [hk]; split_ifs <;> rw [Nat.odd_iff] <;> omega

private lemma case2d_w_odd {e₁ : ℕ} (he : Odd e₁) (hge : e₁ ≥ 3) :
    Odd (e₁ - case2d_u e₁ - case2d_v e₁) := by
  simp only [case2d_u, case2d_v]; obtain ⟨k, hk⟩ := he; rw [hk]
  split_ifs <;> rw [Nat.odd_iff] <;> omega

private lemma case2d_uv_le {e₁ : ℕ} (hge : e₁ ≥ 19) :
    case2d_u e₁ + case2d_v e₁ ≤ e₁ := by
  simp only [case2d_u, case2d_v]; split_ifs <;> omega

private lemma case2d_v_le_u {e₁ : ℕ} : case2d_v e₁ ≤ case2d_u e₁ := by
  simp only [case2d_u, case2d_v]; split_ifs <;> omega

private lemma case2d_w_le_u {e₁ : ℕ} (hge : e₁ ≥ 19) :
    e₁ - (case2d_u e₁ + case2d_v e₁) ≤ case2d_u e₁ := by
  simp only [case2d_u, case2d_v]; split_ifs <;> omega

private lemma case2d_u_pos {e₁ : ℕ} (hge : e₁ ≥ 19) : 0 < case2d_u e₁ := by
  simp only [case2d_u]; omega

private lemma case2d_u_lt {e₁ : ℕ} (hge : e₁ ≥ 19) : case2d_u e₁ < e₁ := by
  simp only [case2d_u]; omega

private lemma case2d_two_u_le {e₁ : ℕ} (he : Odd e₁) (hge : e₁ ≥ 19) :
    2 * case2d_u e₁ ≤ e₁ := by
  simp only [case2d_u]; obtain ⟨k, hk⟩ := he; omega

/-- The base pattern: three alternating bicolor intervals on {0,...,e₁-1}.
    Positions 0..u-1: alternating 0,1 (starts and ends with 0 since u is odd)
    Positions u..u+v-1: alternating 1,2 (starts and ends with 1)
    Positions u+v..e₁-1: alternating 2,0 (starts and ends with 2) -/
private def basePattern (e₁ : ℕ) (j : ℕ) : Fin 3 :=
  let u := case2d_u e₁
  let v := case2d_v e₁
  if j < u then
    if j % 2 = 0 then 0 else 1
  else if j < u + v then
    if (j - u) % 2 = 0 then 1 else 2
  else
    if (j - u - v) % 2 = 0 then 2 else 0

/-- Which interval (0, 1, or 2) a position j falls in. -/
private def whichInterval (e₁ j : ℕ) : Fin 3 :=
  let u := case2d_u e₁
  let v := case2d_v e₁
  if j < u then 0
  else if j < u + v then 1
  else 2

/-- The color pair for each interval. -/
private def intervalColors : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

/-- Any two distinct interval color pairs union to {0, 1, 2}. -/
private lemma intervalColors_union_covers {i₁ i₂ : Fin 3} (h : i₁ ≠ i₂) :
    ∀ k : Fin 3, k ∈ intervalColors i₁ ∨ k ∈ intervalColors i₂ := by
  intro k; fin_cases i₁ <;> fin_cases i₂ <;> fin_cases k <;>
    simp_all [intervalColors, Finset.mem_insert, Finset.mem_singleton]

/-- basePattern(e₁, j) is always in the pair of whichInterval(e₁, j). -/
private lemma basePattern_mem_interval {e₁ j : ℕ} :
    basePattern e₁ j ∈ intervalColors (whichInterval e₁ j) := by
  simp only [basePattern, whichInterval, intervalColors]
  split_ifs with h1 h2 h3 h4 h5 <;>
    simp_all [Finset.mem_insert, Finset.mem_singleton]

/-- Consecutive positions (j, j+1) within the same interval produce
    both colors of that interval. -/
private lemma basePattern_consec_same_interval {e₁ j : ℕ}
    (hsame : whichInterval e₁ j = whichInterval e₁ (j + 1)) :
    {basePattern e₁ j, basePattern e₁ (j + 1)} = intervalColors (whichInterval e₁ j) := by
  simp only [whichInterval, basePattern, intervalColors] at *
  set u := case2d_u e₁
  -- Both j and j+1 are in the same interval; their parities differ
  split_ifs at hsame ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  all_goals (ext x; fin_cases x <;>
    simp_all only [Fin.isValue, mem_insert, mem_singleton] <;> omega)

/-- At an interval boundary (j at end, j+1 at start of next), the pair of
    consecutive basePattern values equals the pair of the left interval. -/
private lemma basePattern_consec_boundary {e₁ j : ℕ}
    (he : Odd e₁) (hge : e₁ ≥ 19) (hj : j < e₁)
    (hdiff : whichInterval e₁ j ≠ whichInterval e₁ ((j + 1) % e₁)) :
    {basePattern e₁ j, basePattern e₁ ((j + 1) % e₁)} =
      intervalColors (whichInterval e₁ j) := by
  obtain ⟨ku, hku⟩ := case2d_u_odd he
  obtain ⟨kv, hkv⟩ := case2d_v_odd he
  obtain ⟨kw, hkw⟩ := case2d_w_odd he (by omega)
  have huv := case2d_uv_le hge
  simp only [whichInterval] at hdiff ⊢
  by_cases hj1_wrap : j + 1 < e₁
  · rw [Nat.mod_eq_of_lt hj1_wrap] at hdiff ⊢
    simp only [basePattern, intervalColors]
    split_ifs at hdiff ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 h9
    all_goals (first | omega | (ext x; fin_cases x <;>
      (simp_all only [Fin.isValue, mem_insert, mem_singleton]; try omega)))
  · -- Wrap: j = e₁ - 1
    push_neg at hj1_wrap
    have hj_eq : j = e₁ - 1 := by omega
    subst hj_eq
    rw [show e₁ - 1 + 1 = e₁ from by omega, Nat.mod_self] at hdiff ⊢
    simp only [basePattern, intervalColors]
    split_ifs at hdiff ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 h9
    all_goals (first | omega | (ext x; fin_cases x <;>
      simp_all only [Fin.isValue, mem_insert, mem_singleton] <;> omega))

/-- Combined: for any j, {basePattern(j), basePattern(j+1 mod e₁)} is the
    interval pair of whichInterval(j). -/
private lemma basePattern_consec_pair {e₁ j : ℕ}
    (he : Odd e₁) (hge : e₁ ≥ 19) (hj : j < e₁) :
    intervalColors (whichInterval e₁ j) ⊆
      {basePattern e₁ j, basePattern e₁ ((j + 1) % e₁)} := by
  by_cases hsame : whichInterval e₁ j = whichInterval e₁ ((j + 1) % e₁)
  · -- Same interval: j+1 < e₁ (otherwise wrap changes interval)
    have hj1 : j + 1 < e₁ := by
      by_contra h
      push_neg at h
      have : j = e₁ - 1 := by omega
      subst this
      rw [show e₁ - 1 + 1 = e₁ from by omega, Nat.mod_self] at hsame
      simp only [whichInterval, case2d_u, case2d_v] at hsame
      split_ifs at hsame <;> omega
    rw [Nat.mod_eq_of_lt hj1]
    exact (basePattern_consec_same_interval (by rwa [Nat.mod_eq_of_lt hj1] at hsame)).ge
  · exact (basePattern_consec_boundary he hge hj hsame).ge

/-- A rotation by r ∈ [u, e₁-u] moves to a different interval:
    whichInterval(j) ≠ whichInterval((j + r) % e₁). -/
private lemma rotation_changes_interval {e₁ j : ℕ}
    (hge : e₁ ≥ 19) (hj : j < e₁)
    {r : ℕ} (hr_lo : case2d_u e₁ ≤ r) (hr_hi : r ≤ e₁ - case2d_u e₁) :
    whichInterval e₁ j ≠ whichInterval e₁ ((j + r) % e₁) := by
  have he₁_pos : 0 < e₁ := by omega
  have huv_bound := case2d_uv_le hge
  have hv_le_u := case2d_v_le_u (e₁ := e₁)
  have hw_le_u := case2d_w_le_u hge
  simp only [whichInterval]
  have hj'_lt : (j + r) % e₁ < e₁ := Nat.mod_lt _ he₁_pos
  intro heq
  by_cases hjr_wrap : j + r < e₁
  · -- No wrap
    rw [Nat.mod_eq_of_lt hjr_wrap] at heq hj'_lt
    split_ifs at heq <;> omega
  · -- Wrap: (j + r) % e₁ = j + r - e₁
    push_neg at hjr_wrap
    have hmod : (j + r) % e₁ = j + r - e₁ := by
      have : r < e₁ := by omega
      have h1 : j + r - e₁ < e₁ := by omega
      rw [Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt this, if_neg (by grind)]
    rw [hmod] at heq hj'_lt
    split_ifs at heq <;> omega

/-- Key polychromaticity lemma: if the base pattern is rotated by r ∈ [u, e₁-u],
    then at every position j, the 2×2 block covers all 3 colors. -/
private lemma basePattern_rotation_covers {e₁ j : ℕ} (he : Odd e₁) (hge : e₁ ≥ 19)
    {r : ℕ} (hr_lo : case2d_u e₁ ≤ r) (hr_hi : r ≤ e₁ - case2d_u e₁)
    (hj : j < e₁) :
    ∀ k : Fin 3, k ∈
      ({basePattern e₁ j, basePattern e₁ ((j + 1) % e₁),
        basePattern e₁ ((j + r) % e₁),
        basePattern e₁ ((j + r + 1) % e₁)} : Finset (Fin 3)) := by
  intro k
  have he₁_pos : 0 < e₁ := by omega
  have hI := rotation_changes_interval hge hj hr_lo hr_hi
  have h1 := basePattern_consec_pair he hge hj
  have hjr : (j + r) % e₁ < e₁ := Nat.mod_lt _ he₁_pos
  have h2 := basePattern_consec_pair he hge hjr
  -- Rewrite ((j + r) % e₁ + 1) % e₁ = (j + r + 1) % e₁
  have hmod : ((j + r) % e₁ + 1) % e₁ = (j + r + 1) % e₁ := by
    conv_rhs => rw [show j + r + 1 = (j + r) + 1 from by ring]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.add_mod]
  rw [hmod] at h2
  have hcov := intervalColors_union_covers hI k
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hcov with hk | hk
  · have := h1 hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  · have := h2 hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto

/-- Existence of a valid wrap rotation: there exists R ∈ [u, e₁-u] mod e₁
    achievable as a sum of (d₁-1) values each in [u, e₁-u].
    Simplified: we just need some R with u ≤ R%e₁ ≤ e₁-u. Since u < e₁-u
    (because u ≤ (e₁+2)/3 < e₁/2 for e₁ ≥ 19), taking R = u works. -/
private lemma exists_valid_wrap_rotation {e₁ : ℕ}
    (hge : e₁ ≥ 19) :
    ∃ R : ℕ, R < e₁ ∧ case2d_u e₁ ≤ R ∧ R ≤ e₁ - case2d_u e₁ := by
  refine ⟨case2d_u e₁, ?_, le_refl _, ?_⟩
  · simp only [case2d_u]; omega
  · simp only [case2d_u]; omega

/-- The orbit map φ(i,j) = i*(b-a) + j*b in ZMod m. -/
private def case2d_orbitMap (m : ℕ) (a b : ℤ) (d₁ e₁ : ℕ) :
    Fin d₁ × Fin e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b

private lemma case2d_addOrderOf_b {m : ℕ} {b : ℤ} {d₁ : ℕ} (hm : 0 < m)
    (hd1_def : Nat.gcd b.natAbs m = d₁) :
    addOrderOf (b : ZMod m) = m / d₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = m / d₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (by omega), Nat.gcd_comm, hd1_def]
  rcases Int.natAbs_eq b with h | h
  · have : (b : ZMod m) = (b.natAbs : ZMod m) := by
      show Int.cast b = Nat.cast b.natAbs
      conv_lhs => rw [h]; rw [Int.cast_natCast]
    rw [this]; exact key
  · have : (b : ZMod m) = -(b.natAbs : ZMod m) := by
      show Int.cast b = -Nat.cast b.natAbs
      conv_lhs => rw [h]; rw [Int.cast_neg, Int.cast_natCast]
    rw [this, addOrderOf_neg]; exact key

private lemma case2d_b_zero_mod_d1 {m : ℕ} {b : ℤ} {d₁ : ℕ}
    (hd1_def : Nat.gcd b.natAbs m = d₁) [NeZero d₁] :
    (b : ZMod d₁) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : d₁ ∣ b.natAbs := hd1_def ▸ Nat.gcd_dvd_left b.natAbs m
  rcases Int.natAbs_eq b with h | h <;> rw [h]
  · exact_mod_cast h1
  · exact dvd_neg.mpr (by exact_mod_cast h1)

private lemma case2d_ba_coprime_d1 {m : ℕ} {a b : ℤ} {d₁ : ℕ}
    (hd1_dvd : d₁ ∣ m)
    (h_gcd_coprime : d₁.gcd (Nat.gcd (b - a).natAbs m) = 1) :
    Nat.Coprime (b - a).natAbs d₁ := by
  rw [Nat.Coprime]
  refine Nat.dvd_one.mp ?_
  calc Nat.gcd (b - a).natAbs d₁
      _ ∣ Nat.gcd d₁ (Nat.gcd (b - a).natAbs m) :=
          Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
            (Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
              (dvd_trans (Nat.gcd_dvd_right _ _) hd1_dvd))
      _ = 1 := h_gcd_coprime

private lemma case2d_ba_unit_d1 {a b : ℤ} {d₁ : ℕ}
    (hba_coprime : Nat.Coprime (b - a).natAbs d₁) :
    IsUnit ((b - a : ℤ) : ZMod d₁) := by
  have h1 : IsUnit ((b - a).natAbs : ZMod d₁) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hba_coprime
  rcases Int.natAbs_eq (b - a) with h | h
  · rwa [h, Int.cast_natCast]
  · rwa [h, Int.cast_neg, Int.cast_natCast, IsUnit.neg_iff]

private lemma case2d_orbitMap_i_eq {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    {i₁ i₂ : Fin d₁} {j₁ j₂ : Fin e₁}
    (heq : case2d_orbitMap m a b d₁ e₁ (i₁, j₁) =
           case2d_orbitMap m a b d₁ e₁ (i₂, j₂)) :
    i₁ = i₂ := by
  simp only [case2d_orbitMap] at heq
  set f := ZMod.castHom hd1_dvd (ZMod d₁)
  have : f ((i₁.val : ZMod m) * ↑(b - a) + (j₁.val : ZMod m) * ↑b) =
      f ((i₂.val : ZMod m) * ↑(b - a) + (j₂.val : ZMod m) * ↑b) := congr_arg f heq
  simp only [map_add, map_mul, map_natCast, map_intCast] at this
  simp only [hb_zero, mul_zero, add_zero] at this
  obtain ⟨u, hu⟩ := hba_unit
  rw [← hu] at this
  have key : (i₁.val : ZMod d₁) = (i₂.val : ZMod d₁) :=
    calc (i₁.val : ZMod d₁)
        = (i₁.val : ZMod d₁) * (↑u * ↑u⁻¹) := by rw [u.mul_inv, mul_one]
      _ = ((i₁.val : ZMod d₁) * ↑u) * ↑u⁻¹ := (mul_assoc _ _ _).symm
      _ = ((i₂.val : ZMod d₁) * ↑u) * ↑u⁻¹ := by rw [this]
      _ = (i₂.val : ZMod d₁) * (↑u * ↑u⁻¹) := mul_assoc _ _ _
      _ = (i₂.val : ZMod d₁) := by rw [u.mul_inv, mul_one]
  ext
  rw [← ZMod.val_natCast_of_lt i₁.isLt, ← ZMod.val_natCast_of_lt i₂.isLt]
  exact congr_arg ZMod.val key

private lemma case2d_orbitMap_j_eq {m : ℕ} {b : ℤ} {e₁ : ℕ}
    (hord : addOrderOf (b : ZMod m) = e₁)
    {j₁ j₂ : Fin e₁}
    (hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m)) :
    j₁ = j₂ := by
  rcases Nat.le_total j₁.val j₂.val with h | h
  · have h3 : (j₂.val - j₁.val) • (b : ZMod m) = 0 :=
      add_left_cancel (a := j₁.val • (b : ZMod m))
        (by rw [add_zero, ← add_nsmul, Nat.add_sub_cancel' h]; exact hj_smul.symm)
    have hdvd : e₁ ∣ (j₂.val - j₁.val) := by
      have := addOrderOf_dvd_of_nsmul_eq_zero h3; rwa [hord] at this
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    ext; omega
  · have h3 : (j₁.val - j₂.val) • (b : ZMod m) = 0 :=
      add_left_cancel (a := j₂.val • (b : ZMod m))
        (by rw [add_zero, ← add_nsmul, Nat.add_sub_cancel' h]; exact hj_smul)
    have hdvd : e₁ ∣ (j₁.val - j₂.val) := by
      have := addOrderOf_dvd_of_nsmul_eq_zero h3; rwa [hord] at this
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    ext; omega

private lemma case2d_orbitMap_injective {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁) :
    Function.Injective (case2d_orbitMap m a b d₁ e₁) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
  have hi := case2d_orbitMap_i_eq hd1_dvd hb_zero hba_unit heq
  subst hi
  simp only [case2d_orbitMap] at heq
  have hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m) := by
    simp only [nsmul_eq_mul]
    exact add_left_cancel heq
  exact Prod.ext rfl (case2d_orbitMap_j_eq hord hj_smul)

private lemma case2d_orbitMap_bijective {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hm_eq : m = d₁ * e₁)
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁) :
    Function.Bijective (case2d_orbitMap m a b d₁ e₁) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨case2d_orbitMap_injective hd1_dvd hb_zero hba_unit hord,
     by simp [Fintype.card_prod, ZMod.card, hm_eq]⟩

private lemma case2d_shift_b {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero e₁]
    (he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∀ p : Fin d₁ × Fin e₁,
      case2d_orbitMap m a b d₁ e₁ p + (b : ZMod m) =
        case2d_orbitMap m a b d₁ e₁ (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [case2d_orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have he1_ge2 : 1 < e₁ := by omega
    have hv : (j + 1 : Fin e₁).val = j.val + 1 := by
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt he1_ge2,
        Nat.mod_eq_of_lt hj]
    rw [hv]; push_cast; ring
  · have hje : j.val + 1 = e₁ := by omega
    have hv : (j + 1 : Fin e₁).val = 0 := by
      simp [Fin.val_add, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      have : (j.val : ZMod m) * ↑b + ↑b = (j.val + 1 : ℕ) • (b : ZMod m) := by
        rw [add_nsmul, one_nsmul, nsmul_eq_mul]
      rw [this, hje, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]

private lemma case2d_shift_ba_no_wrap {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    (i : Fin d₁) (j : Fin e₁) (hi : i.val + 1 < d₁) :
    case2d_orbitMap m a b d₁ e₁ (i, j) + ((b - a : ℤ) : ZMod m) =
      case2d_orbitMap m a b d₁ e₁ (⟨i.val + 1, by omega⟩, j) := by
  simp only [case2d_orbitMap]; push_cast; ring

private lemma case2d_wrap_shift {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁)
    (hm_eq : m = d₁ * e₁)
    (_he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∃ k₀ : Fin e₁,
      (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  haveI : NeZero e₁ :=
    ⟨by intro h; rw [h, mul_zero] at hm_eq; exact (NeZero.ne m) hm_eq⟩
  have hbij := case2d_orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
    set f := ZMod.castHom hd1_dvd (ZMod d₁)
    have hfφ : f (Φ q) = (q.1.val : ZMod d₁) * ((b - a : ℤ) : ZMod d₁) := by
      change f (case2d_orbitMap m a b d₁ e₁ q) = _
      simp only [case2d_orbitMap, map_add, map_mul, map_natCast, map_intCast,
        hb_zero, mul_zero, add_zero]
    rw [hφq] at hfφ
    have hf0 : f (d₁ • ((b - a : ℤ) : ZMod m)) = 0 := by
      rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
    rw [hf0] at hfφ
    have hzmod_zero : (q.1.val : ZMod d₁) = 0 := by
      obtain ⟨u, hu⟩ := hba_unit
      have h : (q.1.val : ZMod d₁) * ↑u = 0 := by rw [hu]; exact hfφ.symm
      calc (q.1.val : ZMod d₁)
          = (q.1.val : ZMod d₁) * 1 := (mul_one _).symm
        _ = (q.1.val : ZMod d₁) * (↑u * ↑u⁻¹) := by rw [u.mul_inv]
        _ = ((q.1.val : ZMod d₁) * ↑u) * ↑u⁻¹ := (mul_assoc _ _ _).symm
        _ = 0 * ↑u⁻¹ := by rw [h]
        _ = 0 := zero_mul _
    have hval := congr_arg ZMod.val hzmod_zero
    rw [ZMod.val_natCast_of_lt q.1.isLt, ZMod.val_zero] at hval
    exact Fin.ext hval
  refine ⟨q.2, ?_⟩
  have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  change case2d_orbitMap m a b d₁ e₁ q = _ at hφq
  simp only [case2d_orbitMap] at hφq
  rw [show q = (q.1, q.2) from (Prod.eta q).symm] at hφq
  simp only [hq_i, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  simp only [nsmul_eq_mul] at hφq ⊢
  exact hφq.symm

private lemma case2d_shift_ba_wrap {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero e₁] [NeZero d₁]
    (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : Fin e₁)
    (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m)) :
    ∀ (j : Fin e₁),
      case2d_orbitMap m a b d₁ e₁
        (⟨d₁ - 1, Nat.sub_one_lt (NeZero.ne d₁)⟩, j) +
        ((b - a : ℤ) : ZMod m) =
        case2d_orbitMap m a b d₁ e₁
          (0, ⟨(j.val + k₀.val) % e₁, Nat.mod_lt _ (NeZero.pos e₁)⟩) := by
  intro j
  simp only [case2d_orbitMap, Fin.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange (d₁-1)*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑(d₁ - 1) : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑(d₁ - 1) : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j * ((b : ℤ) : ZMod m) := by
    rw [← hcast]; ring
  rw [step1]
  -- Step 2: d₁*(b-a) = k₀*b via hk₀
  rw [← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul]
  -- Step 3: k₀*b + j*b = (k₀+j)*b, reorder, convert to nsmul
  rw [← add_mul, ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Step 4: reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  conv_lhs => rw [show n = e₁ * (n / e₁) + n % e₁ from (Nat.div_add_mod n e₁).symm]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]

/-- Given d₁ ≥ 3 values each in [u, e₁-u] can sum to any target mod e₁,
    since the range has width ≥ e₁/3 and d₁ ≥ 3. -/
private lemma case2d_rotation_sum_exists {e₁ d₁ : ℕ}
    (hd1_ge : d₁ ≥ 5) (he1_ge : e₁ ≥ 19) (he1_odd : Odd e₁)
    (target : ℕ) :
    ∃ vals : Fin d₁ → ℕ,
      (∀ i, case2d_u e₁ ≤ vals i ∧ vals i ≤ e₁ - case2d_u e₁) ∧
      (Finset.univ.sum vals) % e₁ = target % e₁ := by
  have hu_lt : case2d_u e₁ < e₁ := by unfold case2d_u; omega
  have h2u : 2 * case2d_u e₁ < e₁ := by
    unfold case2d_u; obtain ⟨k, hk⟩ := he1_odd; omega
  have hdw' : d₁ * (e₁ - 2 * case2d_u e₁) ≥ e₁ := by
    change d₁ * (e₁ - 2 * (e₁ / 3 + e₁ % 3)) ≥ e₁
    obtain ⟨k, hk⟩ := he1_odd; subst hk
    have h5w : 5 * ((2 * k + 1) - 2 * ((2 * k + 1) / 3 + (2 * k + 1) % 3)) ≥
        2 * k + 1 := by omega
    exact le_trans h5w (Nat.mul_le_mul_right _ hd1_ge)
  set u := case2d_u e₁
  set w := e₁ - 2 * u
  have hw_pos : 0 < w := by omega
  have hdw : d₁ * w ≥ e₁ := hdw'
  set deficit := (target + e₁ * d₁ - d₁ * u) % e₁
  have hdef_lt : deficit < e₁ := Nat.mod_lt _ (by omega)
  set q := deficit / w
  set r := deficit % w
  have hr_lt : r < w := Nat.mod_lt _ hw_pos
  have hq_lt : q < d₁ := by
    by_contra hge; push_neg at hge
    have h1 : deficit ≥ d₁ * w :=
      calc deficit ≥ deficit / w * w := Nat.div_mul_le_self deficit w
        _ = q * w := rfl
        _ ≥ d₁ * w := Nat.mul_le_mul_right w hge
    omega
  have hqr : w * q + r = deficit := Nat.div_add_mod deficit w
  let f : Fin d₁ → ℕ := fun i =>
    if i.val < q then e₁ - u else if i.val = q then u + r else u
  refine ⟨f, fun i => ?_, ?_⟩
  · show u ≤ f i ∧ f i ≤ e₁ - u
    simp only [f]; split_ifs <;> omega
  · let g : Fin d₁ → ℕ := fun i =>
      if i.val < q then w else if i.val = q then r else 0
    have hfg : ∀ i : Fin d₁, f i = u + g i := by
      intro i; simp only [f, g]; split_ifs <;> omega
    have hsum_f : Finset.univ.sum f = d₁ * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, Fintype.card_fin]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have hg_split : ∀ i : Fin d₁,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by
        intro i; simp only [g]; split_ifs <;> omega
      rw [Finset.sum_congr rfl (fun i _ => hg_split i), Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          smul_eq_mul]
        congr 1
        trans (Finset.image Fin.val (Finset.univ.filter (fun i : Fin d₁ => i.val < q))).card
        · rw [Finset.card_image_of_injective _ Fin.val_injective]
        · rw [show Finset.image Fin.val (Finset.univ.filter (fun i : Fin d₁ => i.val < q)) =
              Finset.range q from by
            ext j; simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]; constructor
            · rintro ⟨i, hi, rfl⟩; exact hi
            · intro hj; exact ⟨⟨j, lt_trans hj hq_lt⟩, hj, rfl⟩]
          exact Finset.card_range q
      · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have : (Finset.univ.filter (fun i : Fin d₁ => i.val = q)).card = 1 := by
          rw [show Finset.univ.filter (fun i : Fin d₁ => i.val = q) = {⟨q, hq_lt⟩} from by
            ext i; simp [Fin.ext_iff]]
          exact Finset.card_singleton _
        rw [this, one_mul]
    rw [hsum_f, hsum_g, Nat.mul_comm q w, hqr]
    simp only [deficit]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl e₁), ← Nat.add_mod]
    have hle : d₁ * u ≤ target + e₁ * d₁ :=
      le_add_left (le_trans (Nat.mul_le_mul_left d₁ (le_of_lt hu_lt))
        (by rw [Nat.mul_comm]))
    have hadd : d₁ * u + (target + e₁ * d₁ - d₁ * u) = target + e₁ * d₁ :=
      Nat.add_sub_cancel' hle
    rw [hadd, Nat.add_mul_mod_self_left]

private lemma zero_mem_zmod_set (m : ℕ) (a b : ℤ) : (0 : ZMod m) ∈ zmod_set m a b := by
  simp [zmod_set]

private lemma intCast_b_mem_zmod_set (m : ℕ) (a b : ℤ) :
    ((b : ℤ) : ZMod m) ∈ zmod_set m a b := by
  simp [zmod_set]

private lemma intCast_ba_mem_zmod_set (m : ℕ) (a b : ℤ) :
    ((b - a : ℤ) : ZMod m) ∈ zmod_set m a b := by
  simp [zmod_set]

private lemma intCast_2ba_mem_zmod_set (m : ℕ) (a b : ℤ) :
    ((2 * b - a : ℤ) : ZMod m) ∈ zmod_set m a b := by
  simp [zmod_set]

/-- Splitting a Fin filter sum at a boundary -/
private lemma fin_filter_sum_succ {n : ℕ} (f : Fin n → ℕ) (i : Fin n) (_hi : i.val + 1 ≤ n) :
    (Finset.univ.filter (fun k : Fin n => k.val < i.val + 1)).sum f =
    (Finset.univ.filter (fun k : Fin n => k.val < i.val)).sum f + f i := by
  have hsplit : Finset.univ.filter (fun k : Fin n => k.val < i.val + 1) =
      Finset.univ.filter (fun k : Fin n => k.val < i.val) ∪ {i} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hk; by_cases hk' : k.val < i.val
      · left; exact hk'
      · right; ext; omega
    · rintro (hk | hk)
      · omega
      · rw [hk]; omega
  rw [hsplit, Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; intro k hk hk'; omega), Finset.sum_singleton]

/-- When i is the max element, {k | k < i} ∪ {i} = univ. -/
private lemma fin_filter_sum_last {n : ℕ} (f : Fin n → ℕ) (i : Fin n) (hi : i.val = n - 1)
    (hn : 0 < n) :
    (Finset.univ.filter (fun k : Fin n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by
  have hsplit : Finset.univ = Finset.univ.filter (fun k : Fin n => k.val < i.val) ∪ {i} := by
    ext k; simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_filter,
      Finset.mem_singleton]
    by_cases hk : k.val < i.val
    · left; exact ⟨trivial, hk⟩
    · right; ext; omega
  conv_rhs => rw [hsplit]
  rw [Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; intro k hk hk'; omega), Finset.sum_singleton]

-- Position arithmetic helpers for case2d_coloring_works

/-- (a + b % n) % n = (a + b) % n -/
private lemma mod_add_right' (a b n : ℕ) :
    (a + b % n) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd b (dvd_refl n), ← Nat.add_mod]

/-- (a % n + b) % n = (a + b) % n -/
private lemma mod_add_left' (a b n : ℕ) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd a (dvd_refl n), ← Nat.add_mod]

/-- Position shift by 1: adding 1 to Fin coordinate shifts position by 1 mod e₁. -/
private lemma pos_shift_one {n : ℕ} [NeZero n] (j : Fin n) (c : ℕ) :
    ((j + 1 : Fin n).val + c) % n = ((j.val + c) % n + 1) % n := by
  rw [Fin.val_add, Fin.val_one',
    mod_add_right' _ 1, mod_add_left' (j.val + 1) c,
    mod_add_left' (j.val + c) 1]
  congr 1; omega

/-- (j + (S + V) % n) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_succ' (j S V n : ℕ) :
    (j + (S + V) % n) % n = ((j + S % n) % n + V) % n := by
  calc (j + (S + V) % n) % n
      = (j + (S + V)) % n := mod_add_right' j (S + V) n
    _ = (j + S + V) % n := by congr 1; omega
    _ = ((j + S) % n + V) % n := (mod_add_left' (j + S) V n).symm
    _ = ((j + S % n) % n + V) % n := by
        congr 1; exact congrArg (· + V) (mod_add_right' j S n).symm

/-- Wrap case: if (S + V) % n = k₀ % n, then
    (j + k₀) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_wrap' (j S V k₀ n : ℕ)
    (hsum : (S + V) % n = k₀ % n) :
    (j + k₀) % n = ((j + S % n) % n + V) % n := by
  calc (j + k₀) % n
      = (j + k₀ % n) % n := (mod_add_right' j k₀ n).symm
    _ = (j + (S + V) % n) % n := by rw [hsum]
    _ = ((j + S % n) % n + V) % n := pos_shift_succ' j S V n

/-- The coloring for case (2d), connecting to ZMod m. Uses cycle coordinates
    c_{i,j} = i*(b-a) + j*b and the base pattern with rotations. -/
private lemma case2d_coloring_works {m : ℕ} {a b : ℤ}
    (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_odd : Odd (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m))
    (he1_ge : m / Nat.gcd b.natAbs m ≥ 19)
    (h3 : ¬ (3 ∣ Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  set d₁ := Nat.gcd b.natAbs m with hd1_def
  set e₁ := m / d₁ with he1_def
  have hd1_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
  have hd1_pos : 0 < d₁ := by omega
  have he1_pos : 0 < e₁ := by omega
  have hm_pos : 0 < m := by omega
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd1_dvd).symm
  have hd1_gt1 : d₁ > 1 := by omega
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  have hord : addOrderOf (b : ZMod m) = e₁ := case2d_addOrderOf_b (by omega) hd1_def
  have hb_zero : (b : ZMod d₁) = 0 := case2d_b_zero_mod_d1 hd1_def
  have hba_coprime := case2d_ba_coprime_d1 hd1_dvd (by rwa [hd1_def])
  have hba_unit := case2d_ba_unit_d1 hba_coprime
  have he1_b_zero : e₁ • (b : ZMod m) = 0 := by
    rw [← hord]; exact addOrderOf_nsmul_eq_zero _
  have hbij := case2d_orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hd1_dvd hb_zero hba_unit hord hm_eq he1_b_zero
  -- d₁ is odd, > 1, and ¬(3∣d₁), so d₁ ≥ 5
  have hd1_ge5 : d₁ ≥ 5 := by obtain ⟨k, hk⟩ := hd1_odd; omega
  obtain ⟨vals, hvals_bound, hvals_sum⟩ :=
    case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
  -- Cumulative rotation: rot(i) = (Σ_{j<i} vals(j)) % e₁
  let rot : Fin d₁ → ℕ := fun i =>
    ((Finset.univ.filter (fun j : Fin d₁ => j.val < i.val)).sum vals) % e₁
  -- Coloring: χ(x) = basePattern(e₁, (j-coord + rot(i-coord)) % e₁)
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    basePattern e₁ ((coord.2.val + rot coord.1) % e₁)
  refine ⟨χ, fun n k => ?_⟩
  -- χ at orbit coordinates simplifies via Equiv.symm_apply_apply
  have hχ_eq : ∀ (i' : Fin d₁) (j' : Fin e₁),
      χ (Φ (i', j')) = basePattern e₁ ((j'.val + rot i') % e₁) := by
    intro i' j'; simp only [χ, Equiv.symm_apply_apply]
  -- Coordinates of n
  set ij := Φ.symm n
  have hn : Φ ij = n := Equiv.apply_symm_apply Φ n
  set i := ij.1; set j := ij.2
  have hij : ij = (i, j) := (Prod.eta ij).symm
  -- Base position p
  set p := (j.val + rot i) % e₁ with hp_def
  have hp_lt : p < e₁ := Nat.mod_lt _ he1_pos
  -- Shift lemmas
  have hΦ_b : Φ (i, j + 1) = n + ((b : ℤ) : ZMod m) := by
    rw [← hn, hij]; exact (case2d_shift_b he1_b_zero (i, j)).symm
  -- Apply rotation covers
  have covers := basePattern_rotation_covers he1_odd he1_ge
    (hvals_bound i).1 (hvals_bound i).2 hp_lt k
  simp only [Finset.mem_insert, Finset.mem_singleton] at covers
  -- (b-a) shift: case split on i
  by_cases hi : i.val + 1 < d₁
  · -- No-wrap case
    set i' : Fin d₁ := ⟨i.val + 1, hi⟩
    have hΦ_ba : Φ (i', j) = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]; exact (case2d_shift_ba_no_wrap i j hi).symm
    have hΦ_2ba : Φ (i', j + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      have : ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by
        push_cast; ring
      rw [this, ← add_assoc, ← hΦ_ba]
      exact (case2d_shift_b he1_b_zero (i', j)).symm
    -- rot(i') relates to rot(i) via the sum splitting
    have hrot_succ :
        (Finset.univ.filter (fun k : Fin d₁ => k.val < i'.val)).sum vals =
        (Finset.univ.filter (fun k : Fin d₁ => k.val < i.val)).sum vals + vals i := by
      exact fin_filter_sum_succ vals i (by omega)
    rcases covers with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b, by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · exact ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b,
        by rw [← hΦ_b, hχ_eq, h]; congr 1; exact pos_shift_one j (rot i)⟩
    · refine ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_ba, hχ_eq, h]; congr 1
      show (j.val + rot i') % e₁ = (p + vals i) % e₁
      change (j.val + ((Finset.univ.filter
        (fun k : Fin d₁ => k.val < i'.val)).sum vals) % e₁) % e₁ =
        ((j.val + ((Finset.univ.filter
        (fun k : Fin d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
      rw [hrot_succ]
      exact pos_shift_succ' j.val _ (vals i) e₁
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      -- (j+1 + rot i') % e₁ = (p + vals i + 1) % e₁
      -- Use pos_shift_one then the b-a result
      have hba : (j.val + rot i') % e₁ = (p + vals i) % e₁ := by
        change (j.val + ((Finset.univ.filter
          (fun k : Fin d₁ => k.val < i'.val)).sum vals) % e₁) % e₁ =
          ((j.val + ((Finset.univ.filter
          (fun k : Fin d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
        rw [hrot_succ]
        exact pos_shift_succ' j.val _ (vals i) e₁
      calc ((j + 1 : Fin e₁).val + rot i') % e₁
          = ((j.val + rot i') % e₁ + 1) % e₁ := pos_shift_one j (rot i')
        _ = ((p + vals i) % e₁ + 1) % e₁ := by rw [hba]
        _ = (p + vals i + 1) % e₁ := mod_add_left' (p + vals i) 1 e₁
  · -- Wrap case: i = d₁ - 1
    have hi_eq : i.val = d₁ - 1 := by omega
    have hi_fin : i = ⟨d₁ - 1, Nat.sub_one_lt (NeZero.ne d₁)⟩ := by ext; exact hi_eq
    set j' : Fin e₁ := ⟨(j.val + k₀.val) % e₁, Nat.mod_lt _ he1_pos⟩
    have hΦ_ba : Φ (0, j') = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij, hi_fin]; exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ j).symm
    have hΦ_2ba : Φ (0, j' + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      have : ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by
        push_cast; ring
      rw [this, ← add_assoc, ← hΦ_ba]
      exact (case2d_shift_b he1_b_zero (0, j')).symm
    -- rot(0) = 0
    have hrot0 : rot (0 : Fin d₁) = 0 := by
      change (Finset.univ.filter (fun k : Fin d₁ => k.val < (0 : Fin d₁).val)).sum vals % e₁ = 0
      simp
    -- Total sum connects to k₀
    have htotal :
        (Finset.univ.filter (fun k : Fin d₁ => k.val < i.val)).sum vals + vals i =
        Finset.univ.sum vals :=
      fin_filter_sum_last vals i hi_eq (by omega)
    -- Common wrap position result
    have hwrap : (j'.val + rot (0 : Fin d₁)) % e₁ = (p + vals i) % e₁ := by
      rw [hrot0, Nat.add_zero]
      change (j.val + k₀.val) % e₁ % e₁ = (p + vals i) % e₁
      rw [Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁ (by rw [htotal, hvals_sum])
    rcases covers with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b, by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · exact ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b,
        by rw [← hΦ_b, hχ_eq, h]; congr 1; exact pos_shift_one j (rot i)⟩
    · exact ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b,
        by rw [← hΦ_ba, hχ_eq, h]; congr 1⟩
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      calc ((j' + 1 : Fin e₁).val + rot (0 : Fin d₁)) % e₁
          = ((j'.val + rot (0 : Fin d₁)) % e₁ + 1) % e₁ :=
            pos_shift_one j' (rot (0 : Fin d₁))
        _ = ((p + vals i) % e₁ + 1) % e₁ := by rw [hwrap]
        _ = (p + vals i + 1) % e₁ := mod_add_left' (p + vals i) 1 e₁

/-- Subcase (2d): d1 and e1 are both odd, with e1 ≥ 19.
    Uses "rotating" colorings based on partitioning e1 = u + v + w. -/
lemma case_two_odd_large (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_odd : Odd (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m))
    (he1_ge : m / Nat.gcd b.natAbs m ≥ 19)
    (h3 : ¬ (3 ∣ Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) :=
  case2d_coloring_works hm h_gcd_coprime h_min hd1_odd he1_odd he1_ge h3

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
      · have he1_ge : m / Nat.gcd b.natAbs m ≥ 19 := by
          obtain ⟨k, hk⟩ := ho; grind
        by_cases h3 : 3 ∣ Nat.gcd b.natAbs m
        · -- Swap: zmod_set m a b = zmod_set m (-a) (b-a)
          rw [← zmod_set_swap m a b]
          -- After swap, d₁' = gcd((b-a).natAbs, m), and the hypotheses transform
          set a' := (-a : ℤ); set b' := (b - a : ℤ)
          have hba_eq : (b' - a').natAbs = b.natAbs := by
            change (b - a - -a).natAbs = b.natAbs; congr 1; ring
          have h_gcd_coprime' : (Nat.gcd b'.natAbs m).gcd
              (Nat.gcd (b' - a').natAbs m) = 1 := by
            rw [hba_eq]; rwa [Nat.gcd_comm]
          have h_min' : min (Nat.gcd b'.natAbs m)
              (Nat.gcd (b' - a').natAbs m) > 1 := by
            rw [hba_eq]; rwa [min_comm]
          -- Dispatch on swapped parameters' parity/size
          rcases Nat.even_or_odd (m / Nat.gcd b'.natAbs m) with he' | ho'
          · exact case_two_e1_even m a' b' hm h_gcd_coprime' h_min' he'
          · rcases Nat.even_or_odd (Nat.gcd b'.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd m a' b' hm h_gcd_coprime' h_min' hd' ho'
            · by_cases he_le' : m / Nat.gcd b'.natAbs m ≤ 17
              · exact case_two_odd_small m a' b' hm h_gcd_coprime' h_min' hd' ho' he_le'
              · have he1_ge' : m / Nat.gcd b'.natAbs m ≥ 19 := by
                  obtain ⟨k', hk'⟩ := ho'; grind
                -- gcd(d₁, d₁') = 1 and 3∣d₁ implies ¬(3∣d₁')
                have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
                  intro h3d'
                  have h3gcd := Nat.dvd_gcd h3 h3d'
                  rw [h_gcd_coprime] at h3gcd
                  omega
                exact case_two_odd_large m a' b' hm h_gcd_coprime' h_min' hd' ho' he1_ge' h3'
        · exact case_two_odd_large m a b hm h_gcd_coprime h_min hd ho he1_ge h3

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
