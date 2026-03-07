import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Mathlib.Algebra.Ring.AddAut

/-!
# Combinatorial case analysis for the polychromatic coloring theorem

This file contains the main combinatorial argument showing that every 4-element subset
of ℤ admits a 3-polychromatic coloring, under the assumption that the set has been
normalized (via `Main.lean`) to have `c ≥ 289` and `gcd(a,b,c) = 1`.

The proof works in `ZMod m` (where `m = c - a + b`) and splits into two main cases
based on the cycle structure of the group action:

- **Case 1** (`main_case_one`): one of `gcd(b, m)` or `gcd(b-a, m)` equals 1
  (single cycle). The set reduces to `{0, 1, g, g+1}` and is handled by interval
  colorings, multiplication-by-3 reductions to Table 1, or explicit periodic colorings.

- **Case 2** (`main_case_two`): both GCDs exceed 1 (multiple cycles). The set is
  colored via a product decomposition `ZMod d₁ × ZMod e₁ ≅ ZMod m`, with subcases
  based on the parity of `d₁` and `e₁`.

The final assembly is `normal_bit`, which combines both cases.

## Completion status

### Table 1 (Subcase 1a/1c block colorings)
| Lemma | Set | Status |
|---|---|---|
| `table1_0123` | {0,1,2,3} | complete |
| `table1_0134` | {0,1,3,4} | sorry |
| `table1_0235` | {0,2,3,5} | sorry |
| `table1_0347` | {0,3,4,7} | sorry |
| `table1_0358` | {0,3,5,8} | sorry |
| `table1_0145` | {0,1,4,5} | sorry |

### Case 1 — Single Cycle
| Lemma | Subcase | Status |
|---|---|---|
| `case_one_small_g` | (1a) g ∈ {2,3,4} | complete (depends on Table 1) |
| `case_one_interval` | (1b) interval coloring | sorry |
| per-residue lemmas (×6) | (1c) 3 ∤ m | complete (depend on Table 1) |
| `case_one_residues` | (1c) dispatch | complete |
| `case_one_div_g_not_three` | (1d) g ≢ 0 mod 3 | complete |
| `case_one_div_3g` | (1d) m = 3g, 3 ∣ g | complete |
| `case_one_div_3g3` | (1d) m = 3g+3, 3 ∣ g | complete |
| `case_one_divisible` | (1d) dispatch | complete |
| `case_one_dispatch` | Case 1 dispatch | complete |
| `case_one_complement` | WLOG g ≤ m/2 | complete |
| `main_case_one` | Case 1 assembly | complete |

### Case 2 — Multiple Cycles
| Lemma | Subcase | Status |
|---|---|---|
| `case_two_e1_even` | (2a) e₁ even | complete |
| `case_two_d1_even_e1_odd` | (2b) d₁ even, e₁ odd | sorry |
| `case_two_odd_small` | (2c) both odd, e₁ ≤ 17 | sorry |
| `case_two_odd_large` | (2d) both odd, e₁ ≥ 19 | sorry |
| `main_case_two` | Case 2 dispatch | complete |

### Assembly
| Lemma | Status |
|---|---|
| `zmod_set_card_eq_four` | complete |
| `gcd_coprime_of_gcd_abc` | complete |
| `hasPolychromColouring_of_zmod_set` | complete |
| `normal_bit` | complete (modulo sorry dependencies) |

Total: 9 sorries (5 Table 1 + 1 interval + 3 Case 2)
-/

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

/-! ## Table 1: Block concatenation colorings (paper §4, Table 1)

For each set S below, blocks of length r and r+1 (prepending 0 to the period-r block)
can be concatenated in any order to produce an S-polychromatic 3-coloring of ℤ_m.
The Frobenius coin problem ensures m can be so expressed when m > r² - r - 1.
Since all uses have m ≥ 289, the bounds below always hold.

These are used in subcases (1a) and (1c) of Main Case 1.
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

/-! ## Main Case 1: Single Cycle (paper §4.1)

When one of `gcd(b, m)` or `gcd(b-a, m)` equals 1, the action of `b` (or `b-a`) on
`ZMod m` is a single cycle. The set `zmod_set m a b` reduces to `{0, 1, g, g+1}` via
multiplication by a unit (see `exists_g_of_coprime`). The proof then splits:

- **(1a)** `g ∈ {2,3,4}`: reduces directly to Table 1 entries.
- **(1b)** General `g`: an interval coloring of `ZMod m` into `s` blocks (smallest
  multiple of 3 with `g > ⌈m/s⌉`) works when `g < 2⌊m/s⌋`.
- **(1c)** `3 ∤ m`, `s = 6`: multiplication by 3 (a unit in `ZMod m`) maps `{0,1,g,g+1}`
  to a translate of a Table 1 set. Six per-residue lemmas handle `m mod 3g`.
- **(1d)** `3 ∣ m`, `s = 6`: explicit periodic colorings of period `g` or `g+1`.
-/

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

/-- Subcase (1b): interval coloring strategy.
    Let s be the smallest multiple of 3 such that g > ⌈m/s⌉. Split Z_m into s
    intervals of lengths ⌊m/s⌋ and ⌈m/s⌉, colored in a repeating 01/12/20
    pattern (repeated s/3 times). Since ⌈m/s⌉ < g < 2⌊m/s⌋, any translate of
    {0,1,g,g+1} where the pairs {0,1} and {g,g+1} lie in different intervals gets
    all three colors. If one pair straddles two consecutive intervals, it gets only the
    single color common to these two intervals, but the other pair lies fully inside
    a third interval which is colored with the remaining two colors. -/
lemma case_one_interval (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
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

/-! ### Subcase (1c): per-residue lemmas (paper §4.1, case 3 ∤ m)

Each lemma reduces `{0, 1, g, g+1}` to a translate of a Table 1 set via
multiplication by 3 (which is an automorphism of `ZMod m` when `3 ∤ m`).
The six cases correspond to `m mod 3` and the value of `g` relative to `m/3`.
-/

/-- m = 3g - 2: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,2,3,5}. -/
lemma case_one_res_3g_sub_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (show ¬3 ∣ m by grind)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = 2 := by
    simpa using show ((3 * g : ℕ) : ZMod m) = (m + 2 : ℕ) from by congr 1; grind
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
    simpa using show ((3 * g : ℕ) : ZMod m) = (m + 1 : ℕ) from by congr 1; grind
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
      ZMod.natCast_self] at this; grind
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
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this; grind
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
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this; grind
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
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] at this; grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = -2 := by grind
  have : {0, (3 : ZMod m), -5, -2} = (-5 : ZMod m) +ᵥ ({0, 3, 5, 8} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0358 m (by grind)

/-- Subcase (1c) assembled: dispatches to the six per-residue lemmas above.
    Covers the case `3 ∤ m` with `2⌊m/6⌋ ≤ g ≤ ⌈m/3⌉` (paper §4.1). -/
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

/-! ### Subcase (1d): 3 ∣ m, split by g mod 3 (paper §4.1, case 3 ∣ m)

When `3 ∣ m`, multiplication by 3 is not available. Instead:
- If `g ≢ 0 (mod 3)`: the uniform coloring `n ↦ n mod 3` works directly.
- If `g ≡ 0 (mod 3)` and `m = 3g`: a diagonal coloring `n ↦ (n mod 3 + n/g) mod 3`.
- If `g ≡ 0 (mod 3)` and `m = 3g+3`: a reversed diagonal coloring of period `g+1`.
-/

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
  rcases show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by grind with h | h | h <;>
    grind [Nat.add_mod, Nat.mod_self, Nat.mod_mod]

private lemma color_shift_q (r q : ℕ) :
    (r % 3 + (3 - (q + 1) % 3)) % 3 =
      ((r % 3 + (3 - q % 3)) % 3 + 2) % 3 := by
  rcases show q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 from by grind with h | h | h <;>
    grind [Nat.add_mod, Nat.mod_self, Nat.mod_mod]

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
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = k.val := by
  obtain ⟨h1, h2, h3⟩ := mod3_witness hs k.isLt
  set d := (k.val + 3 - s) % 3
  have : d = 0 ∨ d = 1 ∨ d = 2 := by grind
  rcases this with h | h | h
  exacts [⟨a₀, ha₀, hc₀ ▸ h1 h⟩, ⟨a₁, ha₁, hc₁ ▸ h2 h⟩, ⟨a₂, ha₂, hc₂ ▸ h3 h⟩]

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
       have : (n + (a : ZMod m)).val = (n.val + a) % m := by
         rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt]
       rw [this, hc_period, hca]⟩

/-- (1d), m = 3g, g ≡ 0 (mod 3): diagonal coloring `n ↦ (n%3 + n/g) % 3`. -/
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
    rw [Nat.mod_mod_of_dvd p (dvd_mul_right 3 g)]
    have h1 : (3 * (p / (3 * g))) * g = 3 * g * (p / (3 * g)) :=
      by ring
    have h2 : p = p % (3 * g) + (3 * (p / (3 * g))) * g := by
      rw [h1]; exact (Nat.mod_add_div p (3 * g)).symm
    have h3 : p / g = p % (3 * g) / g + 3 * (p / (3 * g)) := by
      conv_lhs => rw [h2]; exact Nat.add_mul_div_right _ _ hg
    conv_rhs => rw [h3]
    grind
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val; set r := v % g; set q := v / g
  have hv_eq : v = g * q + r := (Nat.div_add_mod v g).symm
  have hr_lt : r < g := Nat.mod_lt _ hg
  have color_at : ∀ q' r', r' < g →
      c (g * q' + r') = (r' % 3 + q') % 3 := fun q' r' hr' => by
    have gk_mod3 : (g * q' + r') % 3 = r' % 3 := by
      rw [ht, show 3 * t * q' + r' = 3 * (t * q') + r' from by ring,
          Nat.mul_add_mod]
    simp only [c, gk_mod3, Nat.mul_add_div hg,
      Nat.div_eq_of_lt hr', add_zero]
  by_cases hr_lt_gm1 : r + 1 < g
  · have hcv : c v = (r % 3 + q) % 3 := hv_eq ▸ color_at q r hr_lt
    have hcvg : c (v + g) = (r % 3 + (q + 1)) % 3 := by
      rw [show v + g = g * (q + 1) + r from by grind,
          color_at (q + 1) r hr_lt]
    have hcvg1 : c (v + g + 1) = ((r + 1) % 3 + (q + 1)) % 3 := by
      rw [show v + g + 1 = g * (q + 1) + (r + 1) from by grind,
          color_at (q + 1) (r + 1) (by grind)]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g (g + 1)
      (by simp) (by simp) (by simp)
      hcv (by grind)
        (by grind)
  · have hr_eq : r = g - 1 := by grind
    have hcv : c v = (2 + q) % 3 := by grind
    have hcv1 : c (v + 1) = (q + 1) % 3 := by
      rw [show v + 1 = g * (q + 1) + 0 from by grind,
          color_at (q + 1) 0 hg]; simp
    have hcvg : c (v + g) = (2 + (q + 1)) % 3 := by
      have : v + g = g * (q + 1) + (g - 1) := by grind
      rw [this, color_at (q + 1) (g - 1) (by grind)]
      have : g - 1 = 3 * t - 1 := by grind
      rw [this]; grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)

/-- (1d), m = 3g+3, g ≡ 0 (mod 3): reversed diagonal coloring of period `g+1`. -/
lemma case_one_div_3g3 (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  set h := g + 1
  have hh_pos : 0 < h := by grind
  let c (p : ℕ) : ℕ := (p % h % 3 + (3 - p / h % 3)) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    have hm3h : m = 3 * h := by grind
    intro p; simp only [c, hm3h]
    conv_rhs => rw [show p = h * (3 * (p / (3 * h))) + p % (3 * h) from by linarith
      [(Nat.mod_add_div p (3 * h)).symm]]
    grind [Nat.mul_add_mod, Nat.add_mul_div_left]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val; set r := v % h; set q := v / h
  have hv_eq : v = h * q + r := (Nat.div_add_mod v h).symm
  have hr_lt : r < h := Nat.mod_lt _ hh_pos
  have color_at : ∀ q' r', r' < h →
      c (h * q' + r') = (r' % 3 + (3 - q' % 3)) % 3 := fun q' r' hr' => by
    change ((h * q' + r') % h % 3 + (3 - (h * q' + r') / h % 3)) % 3 = _
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr',
        Nat.mul_add_div hh_pos, Nat.div_eq_of_lt hr', add_zero]
  by_cases hrg : r = g
  · have hcv : c v = (3 - q % 3) % 3 := by grind
    have hcvg : c (v + g) = (2 + (3 - (q + 1) % 3)) % 3 := by
      rw [show v + g = h * (q + 1) + (g - 1) from by grind,
          color_at (q + 1) (g - 1) (by grind), ht,
          show 3 * t - 1 = 3 * (t - 1) + 2 from by grind]; simp
    have hcv1 : c (v + 1) = (3 - (q + 1) % 3) % 3 := by
      rw [show v + 1 = h * (q + 1) + 0 from by grind,
          color_at (q + 1) 0 (by grind)]; grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)
  · have hcv1 : c (v + 1) = ((r + 1) % 3 + (3 - q % 3)) % 3 := by
      rw [show v + 1 = h * q + (r + 1) from by grind,
          color_at q (r + 1) (by grind)]
    have hcvg1 :
        c (v + g + 1) = (r % 3 + (3 - (q + 1) % 3)) % 3 := by
      rw [show v + g + 1 = h * (q + 1) + r from by grind,
          color_at (q + 1) r hr_lt]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 1 (g + 1)
      (by simp) (by simp) (by simp) rfl
      (by rw [hcv1]; exact color_shift_r r q)
      (by have : v + (g + 1) = v + g + 1 := by ring
          rw [this, hcvg1]; exact color_shift_q r q)

/-- Subcase (1d) assembled: dispatches on `g % 3` and `m ∈ {3g, 3g+3}` (paper §4.1). -/
lemma case_one_divisible (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  by_cases hg3 : g % 3 = 0
  · rcases h_div with h | h
    · exact case_one_div_3g m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
    · exact case_one_div_3g3 m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
  · exact case_one_div_g_not_three m g h_div hg3

/-- Combined dispatch: applies subcases (1a)–(1d) for 2 ≤ g ≤ m/2 and m ≥ 289.
    Let s be the smallest multiple of 3 such that g > ⌈m/s⌉.
    - (1a): g ∈ {2,3,4}, handled by Table 1 entries
    - (1b): 5 ≤ g < 2⌊m/s⌋, handled by the interval coloring
    - (1c): 2⌊m/s⌋ ≤ g ≤ ⌈m/(s-3)⌉ with 3 ∤ m (paper shows s = 6 here),
            handled by multiplying by 3 and reducing to Table 1
    - (1d): 2⌊m/s⌋ ≤ g ≤ ⌈m/(s-3)⌉ with 3 ∣ m (paper shows s = 6 here),
            handled by explicit periodic colorings -/
lemma case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g)
    (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  -- (1a): small g
  by_cases hg4 : g ≤ 4
  · exact case_one_small_g m g hm (by grind)
  · push_neg at hg4
    -- For g ≥ 5, let s be the smallest multiple of 3 such that g > ⌈m/s⌉.
    -- The paper shows: for m ≥ 289, either g < 2⌊m/s⌋ (subcase 1b) or
    -- s = 6 and 2⌊m/6⌋ ≤ g ≤ ⌈m/3⌉ (subcases 1c/1d).
    -- We split on whether g falls in the (1c)/(1d) range.
    by_cases hg_lb6 : 2 * (m / 6) ≤ g
    · by_cases hg_ub3 : g ≤ (m + 2) / 3
      · -- s = 6: subcases (1c) and (1d)
        by_cases h3 : m % 3 = 0
        · exact case_one_divisible m g hm (by grind)
        · exact case_one_residues m g hm h3 ⟨hg_lb6, hg_ub3⟩
      · -- g > ⌈m/3⌉: (1b) with s = 3
        push_neg at hg_ub3
        exact case_one_interval m 3 g (by grind) ⟨1, rfl⟩
          (by grind) (by grind : g < 2 * (m / 3))
    · -- g < 2⌊m/6⌋: (1b), find appropriate s
      push_neg at hg_lb6
      -- s is the smallest multiple of 3 with g > ⌈m/s⌉.
      -- The condition g < 2⌊m/s⌋ follows from g ≤ ⌈m/(s-3)⌉.
      by_cases h6 : (m + 5) / 6 < g
      · -- s = 6 works: ⌈m/6⌉ < g and g < 2⌊m/6⌋
        exact case_one_interval m 6 g (by grind) ⟨2, rfl⟩ h6 hg_lb6
      · -- s ≥ 9: use s = 3⌈m/(3(g-1))⌉
        push_neg at h6
        have h3g1 : 0 < 3 * (g - 1) := by grind
        set q := (m - 1) / (3 * (g - 1))
        have hq_lb : q * (3 * (g - 1)) ≤ m - 1 := Nat.div_mul_le_self _ _
        have hq2 : q ≥ 2 := by
          by_contra hlt; push_neg at hlt
          exact absurd ((Nat.div_lt_iff_lt_mul h3g1).mp hlt) (by grind)
        have hq_ub : m - 1 < 3 * (g - 1) * (q + 1) := Nat.lt_mul_div_succ _ h3g1
        have hm_lb : m ≥ q * (3 * (g - 1)) + 1 := by
          grind
        exact case_one_interval m (3 * (q + 1)) g (by grind) ⟨q + 1, rfl⟩
          (by -- ⌈m/s⌉ < g
            rw [Nat.div_lt_iff_lt_mul (by grind : 0 < 3 * (q + 1))]
            have : g * (3 * (q + 1)) = (g - 1 + 1) * (3 * (q + 1)) := by grind
            grind)
          (by -- g < 2⌊m/s⌋
            suffices h : (g + 2) / 2 ≤ m / (3 * (q + 1)) by grind
            rw [Nat.le_div_iff_mul_le (by grind : 0 < 3 * (q + 1))]
            suffices (g + 2) * (3 * (q + 1)) ≤ 2 * m by
              have := Nat.div_mul_le_self (g + 2) 2; nlinarith
            by_cases hg10 : g ≥ 10
            · have : g ≥ 1 := by grind
              zify [this] at hm_lb ⊢; nlinarith
            · have : g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 := by grind
              rcases this with rfl | rfl | rfl | rfl | rfl <;> grind)

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
  have hinj : Function.Injective (bz * · : ZMod m → ZMod m) := fun x y h => by
    simpa [← mul_assoc, ZMod.inv_mul_of_unit _ hub] using congr_arg (bz⁻¹ * ·) h
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

/-! ## Main Case 2: Multiple Cycles (paper §4.2)

When both `gcd(b, m) > 1` and `gcd(b-a, m) > 1`, the action of `b` on `ZMod m`
decomposes into `d₁ = gcd(b, m)` cycles of length `e₁ = m / d₁`. We use the
product decomposition `ZMod d₁ × ZMod e₁ ≅ ZMod m` to define colorings.

Each translate of `{0, b-a, b, 2b-a}` touches two adjacent cycles (via `b-a`)
and two consecutive positions within each cycle (via `b`). The coloring assigns
each cycle a pair of colors that alternate along the cycle, chosen so that
adjacent cycles collectively cover all three colors.

- **(2a)** `e₁` even: parity alternation within each cycle gives two colors per
  cycle; the three "missing color" categories (even/odd/last) ensure coverage.
- **(2b)** `d₁` even, `e₁` odd: similar but with swapped roles.
- **(2c)** Both odd, `e₁ ≤ 17`: handled by specific small patterns.
- **(2d)** Both odd, `e₁ ≥ 19`: "rotating" colorings based on a partition `e₁ = u+v+w`.
-/

section Case2_MultipleCycles

variable (m : ℕ) (a b : ℤ)

-- In this section, we work directly with `zmod_set` using cycle decompositions.
-- We inline d1 = gcd(b, m) and e1 = m / d1.

private lemma zmod_val_add_one (d : ℕ) [NeZero d] (hd : d ≥ 2) (i : ZMod d) :
    (i + 1).val = if i.val + 1 < d then i.val + 1 else 0 := by
  have hival : (i + 1).val = (i.val + 1) % d := by
    rw [ZMod.val_add]; congr 1
    haveI : Fact (1 < d) := ⟨by omega⟩
    simp [ZMod.val_one]
  rw [hival]; split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have := i.val_lt (n := d)
    grind [Nat.mod_self]

private lemma parity_flip_even (e : ℕ) [NeZero e] (he : Even e) (he2 : e ≥ 2)
    (j : ZMod e) : j.val % 2 ≠ (j + 1).val % 2 := by
  rw [zmod_val_add_one e he2 j]
  obtain ⟨k, hk⟩ := he
  have := j.val_lt (n := e)
  split_ifs <;> grind

-- The coloring function for the even-parity cycle decomposition (Case 2a).
-- Each cycle uses two colors that alternate with parity; the last cycle (when d₁ is
-- odd) uses {1,2}, even-indexed cycles use {0,1}, odd-indexed cycles use {0,2}.
private def cycle_coloring (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
  if i.val = d₁ - 1 ∧ ¬Even d₁ then ⟨1 + j.val % 2, by omega⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by omega⟩
  else ⟨2 * (j.val % 2), by omega⟩

-- The "missing" color for each cycle category.
-- Category A (even, not special last): misses 2
-- Category B (odd, not special last): misses 1
-- Category C (last cycle, d₁ odd): misses 0
private def missing_color (d₁ : ℕ) (i : ZMod d₁) : Fin 3 :=
  if i.val = d₁ - 1 ∧ d₁ % 2 = 1 then 0
  else if i.val % 2 = 0 then 2
  else 1

-- Fin 3 fact: if a ≠ b, a ≠ c, b ≠ c, and k ≠ c, then k = a ∨ k = b.
private lemma fin3_eq_of_ne {a b c k : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hkc : k ≠ c) :
    k = a ∨ k = b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases k <;> simp_all

-- cycle_coloring(i, j) never equals the missing color of cycle i.
private lemma f_ne_missing_color (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (i : ZMod d₁) (j : ZMod e₁) :
    cycle_coloring d₁ e₁ (i, j) ≠ missing_color d₁ i := by
  simp only [cycle_coloring, missing_color, Nat.even_iff]
  split_ifs <;> grind [Fin.ext_iff]

-- Adjacent cycles have different missing colors.
private lemma missing_color_ne_succ (d₁ : ℕ) [NeZero d₁] (hd₁ : d₁ ≥ 2)
    (i : ZMod d₁) : missing_color d₁ i ≠ missing_color d₁ (i + 1) := by
  simp only [missing_color]
  have hi := i.val_lt (n := d₁)
  have hi1 := zmod_val_add_one d₁ hd₁ i
  have : ((i + 1).val = i.val + 1 ∧ i.val + 1 < d₁) ∨
      ((i + 1).val = 0 ∧ i.val + 1 = d₁) := by
    rw [hi1]; split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, by omega⟩
  rcases this with ⟨hi1_eq, _⟩ | ⟨hi1_eq, _⟩ <;>
  simp only [hi1_eq] <;>
  (split_ifs <;> grind [Fin.ext_iff])

-- cycle_coloring(i,j) ≠ cycle_coloring(i,j+1) when parity flips.
private lemma f_alt_color (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d₁) (j : ZMod e₁) :
    cycle_coloring d₁ e₁ (i, j) ≠ cycle_coloring d₁ e₁ (i, j + 1) := by
  simp only [cycle_coloring]
  have := hparity j
  split_ifs <;> grind [Fin.ext_iff]

-- Coverage: adjacent cycles cover all 3 colors.
private lemma color_covers_even (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (hd₁_ge2 : d₁ ≥ 2) (_he₁_ge2 : e₁ ≥ 2)
    (hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d₁) (j₁ j₂ : ZMod e₁) (k : Fin 3) :
    k = cycle_coloring d₁ e₁ (i, j₁) ∨
    k = cycle_coloring d₁ e₁ (i, j₁ + 1) ∨
    k = cycle_coloring d₁ e₁ (i + 1, j₂) ∨
    k = cycle_coloring d₁ e₁ (i + 1, j₂ + 1) := by
  -- Either k is not the missing color of cycle i, or it is.
  by_cases hk : k = missing_color d₁ i
  · -- k = missing_color(i), so k ≠ missing_color(i+1)
    have hk_ne : k ≠ missing_color d₁ (i + 1) := hk ▸ missing_color_ne_succ d₁ hd₁_ge2 i
    rcases fin3_eq_of_ne (f_alt_color d₁ e₁ hparity (i + 1) j₂)
      (f_ne_missing_color d₁ e₁ (i + 1) j₂)
      (f_ne_missing_color d₁ e₁ (i + 1) (j₂ + 1)) hk_ne with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · -- k ≠ missing_color(i), so k appears in {f(i,j₁), f(i,j₁+1)}
    rcases fin3_eq_of_ne (f_alt_color d₁ e₁ hparity i j₁)
      (f_ne_missing_color d₁ e₁ i j₁)
      (f_ne_missing_color d₁ e₁ i (j₁ + 1)) hk with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

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
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd₁_dvd).symm
  have he₁_ge2 : e₁ ≥ 2 := by
    have : 0 < e₁ := Nat.div_pos (Nat.le_of_dvd (by omega) hd₁_dvd) hd₁_pos
    obtain ⟨k, hk⟩ := he1_even; grind
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  -- d₁ divides b (ℤ level)
  have hd₁_dvd_b : (d₁ : ℤ) ∣ b := by
    have := Int.gcd_dvd_left b (m : ℤ)
    simp only [Int.gcd, Int.natAbs_natCast] at this; exact this
  -- b ≡ 0 mod d₁
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd₁_dvd_b
  -- (b-a) is a unit in ZMod d₁
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (by
      have h1 : (b - a).natAbs.gcd d₁ ∣ d₁ := Nat.gcd_dvd_right _ _
      have h2 : (b - a).natAbs.gcd d₁ ∣ (b - a).natAbs.gcd m :=
        Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_right _ _) hd₁_dvd)
      exact Nat.eq_one_of_dvd_one (h_gcd_coprime ▸ Nat.dvd_gcd h1 h2))
  -- b/d₁ is coprime to e₁
  obtain ⟨q, hq⟩ := hd₁_dvd_b
  have hq_cop : Nat.Coprime q.natAbs e₁ := by
    rw [show q.natAbs = b.natAbs / d₁ from by
      rw [hq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hd₁_pos]]
    exact Nat.coprime_div_gcd_div_gcd hd₁_pos
  -- e₁ * b ≡ 0 mod m
  have he₁b_zero : (e₁ : ZMod m) * (Int.cast b : ZMod m) = 0 := by
    rw [hq]; push_cast
    have : (e₁ * d₁ : ℕ) = m := by linarith [hm_eq]
    rw [show (e₁ : ZMod m) * ((d₁ : ZMod m) * (q : ZMod m)) =
      ((e₁ * d₁ : ℕ) : ZMod m) * (q : ZMod m) from by push_cast; ring, this]; simp
  -- Key lemma: congruence mod e₁ is invisible after ×b in ZMod m
  have hmod_b : ∀ n₁ n₂ : ℤ, (e₁ : ℤ) ∣ (n₁ - n₂) →
      (↑n₁ : ZMod m) * ↑b = (↑n₂ : ZMod m) * ↑b := by
    intro n₁ n₂ ⟨k, hk⟩
    suffices ((n₁ - n₂ : ℤ) : ZMod m) * ↑b = 0 by
      rwa [Int.cast_sub, sub_mul, sub_eq_zero] at this
    rw [hk]; push_cast
    have : (↑e₁ * k : ZMod m) * ↑b = k * ((e₁ : ZMod m) * ↑b) := by ring
    rw [this, he₁b_zero, mul_zero]
  -- Define the cycle map φ : ZMod d₁ × ZMod e₁ → ZMod m
  let φ : ZMod d₁ × ZMod e₁ → ZMod m :=
    fun ⟨i, j⟩ => (i.val : ZMod m) * ↑(b - a) + (j.val : ZMod m) * ↑b
  -- φ(i, j+1) = φ(i, j) + b
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; simp only [φ]
    suffices ((j + 1).val : ZMod m) * (↑b : ZMod m) = (j.val : ZMod m) * ↑b + ↑b by
      rw [this]; ring
    have hrhs : (j.val : ZMod m) * ↑b + ↑b = ((j.val : ℤ) + 1 : ZMod m) * ↑b := by
      push_cast; ring
    rw [hrhs]
    have hval : (j + 1).val = (j.val + 1) % e₁ := by
      rw [ZMod.val_add]; congr 1
      haveI : Fact (1 < e₁) := ⟨by omega⟩; simp [ZMod.val_one]
    have hdvd : (↑e₁ : ℤ) ∣ (↑(j + 1).val : ℤ) - ((↑j.val : ℤ) + 1) :=
      ⟨-↑((j.val + 1) / e₁), by
        have := congr_arg (Nat.cast (R := ℤ)) hval
        have := Nat.div_add_mod (j.val + 1) e₁; push_cast at *; linarith⟩
    exact_mod_cast hmod_b ((j + 1).val : ℤ) ((j.val : ℤ) + 1) hdvd
  -- Cycle index function α : ZMod m → ZMod d₁
  obtain ⟨u_ba, hu_ba⟩ := hba_unit
  let α : ZMod m → ZMod d₁ :=
    fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
  -- α(x + (b-a)) = α(x) + 1
  have hα_ba : ∀ x, α (x + ↑(b - a)) = α x + 1 := by
    intro x; simp only [α, map_add, map_intCast, add_mul]
    rw [← hu_ba]; ring_nf; rw [u_ba.inv_mul]; ring
  -- α(φ(i, j)) = i
  have hα_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (φ (i, j)) = i := by
    intro i j; simp only [α, φ]
    rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast, map_intCast,
      hb_zero, mul_zero, add_zero, mul_assoc, ← hu_ba, u_ba.mul_inv, mul_one]
    simp [ZMod.natCast_val]
  -- φ is injective
  have hφ_inj : Function.Injective φ := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
    have hi : i₁ = i₂ := by
      have h1 := hα_φ i₁ j₁; have h2 := hα_φ i₂ j₂
      rw [h] at h1; exact h1.symm.trans h2
    subst hi; congr 1
    have hj_eq : (↑j₁.val : ZMod m) * ↑b = (↑j₂.val : ZMod m) * ↑b :=
      add_left_cancel (h : (↑i₁.val : ZMod m) * ↑(b - a) + _ = _ + _)
    have h_dvd : (m : ℤ) ∣ ((j₁.val : ℤ) - j₂.val) * b := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have : ((j₁.val : ZMod m) - (j₂.val : ZMod m)) * (↑b : ZMod m) = 0 := by
        rw [sub_mul]; exact sub_eq_zero.mpr hj_eq
      convert this using 1; push_cast; ring
    have h_dvd2 : (e₁ : ℤ) ∣ ((j₁.val : ℤ) - j₂.val) * q := by
      rw [hq] at h_dvd
      exact (mul_dvd_mul_iff_left (by positivity : (d₁ : ℤ) ≠ 0)).mp (by
        convert h_dvd using 1 <;> [linarith [hm_eq]; ring])
    have h_nat : e₁ ∣ ((j₁.val : ℤ) - j₂.val).natAbs := by
      have h1 : e₁ ∣ (((j₁.val : ℤ) - j₂.val) * q).natAbs := by
        rwa [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
      rw [Int.natAbs_mul] at h1
      exact hq_cop.symm.dvd_of_dvd_mul_right h1
    apply ZMod.val_injective
    have := Nat.eq_zero_of_dvd_of_lt h_nat (by
      have := j₁.val_lt (n := e₁); have := j₂.val_lt (n := e₁); omega)
    rwa [Int.natAbs_eq_zero, sub_eq_zero, Nat.cast_inj] at this
  -- φ is bijective
  have hφ_bij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr
      ⟨hφ_inj, by simp [Fintype.card_prod, ZMod.card, hm_eq]⟩
  let Φ := Equiv.ofBijective φ hφ_bij
  -- Φ.symm(x+b) = (same_i, j+1)
  have hΦ_add_b : ∀ x : ZMod m,
      Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := fun x => by
    have key := hφ_add_b (Φ.symm x).1 (Φ.symm x).2
    change Φ ((Φ.symm x).1, (Φ.symm x).2 + 1) = Φ (Φ.symm x) + ↑b at key
    rw [Equiv.apply_symm_apply] at key
    rw [← key, Equiv.symm_apply_apply]
  -- (Φ.symm x).1 = α x
  have hΦ_cycle : ∀ x : ZMod m, (Φ.symm x).1 = α x := fun x => by
    have h := hα_φ (Φ.symm x).1 (Φ.symm x).2
    change α (Φ (Φ.symm x)) = _ at h
    rw [Equiv.apply_symm_apply] at h; exact h.symm
  have hd₁_ge2 : d₁ ≥ 2 := by
    have := Nat.min_le_left (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m)
    grind
  have hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2 :=
    parity_flip_even e₁ he1_even he₁_ge2
  -- Define coloring and prove polychromaticity
  let χ : ZMod m → Fin 3 := cycle_coloring d₁ e₁ ∘ Φ.symm
  let f := cycle_coloring d₁ e₁
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set p := Φ.symm n; set i := p.1; set j := p.2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := congr_arg f (hΦ_add_b n)
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') :=
    congr_arg f (Prod.ext (by rw [hΦ_cycle, hα_ba, ← hΦ_cycle]) rfl)
  have hχ_n2ba : χ (n + ↑(2 * b - a)) = f (i + 1, j' + 1) := by
    have : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by push_cast; ring
    rw [congr_arg χ this]
    have hΦ' := hΦ_add_b (n + ↑(b - a))
    exact congr_arg f (Prod.ext
      (by rw [Prod.ext_iff.mp hΦ' |>.1, hΦ_cycle, hα_ba, ← hΦ_cycle])
      (Prod.ext_iff.mp hΦ' |>.2))
  rcases color_covers_even d₁ e₁ hd₁_ge2 he₁_ge2 hparity i j j' k with h | h | h | h
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
      · have : m / Nat.gcd b.natAbs m ≥ 19 := by grind
        exact case_two_odd_large m a b hm h_gcd_coprime h_min hd ho this

end Case2_MultipleCycles

/-! ## Assembly

The remaining lemmas connect the `ZMod m` analysis back to `ℤ`: cardinality of
`zmod_set`, the GCD coprimality reduction, and the final theorem `normal_bit`
which dispatches on `min(d₁, d₂) = 1` vs `> 1`.
-/

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

/-- The main theorem (paper §4): combines the reduction to `ZMod m` with the
    Case 1 / Case 2 split on `min(gcd(b, m), gcd(b-a, m))`. -/
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
