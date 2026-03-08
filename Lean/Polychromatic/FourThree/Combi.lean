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
| `case_two_d1_even_e1_odd` | (2b) d₁ even, e₁ odd | complete |
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
    grind
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
      have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by grind
      rcases this with rfl | rfl | rfl | rfl <;> simp
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
          have : kv = 0 ∨ kv = 1 ∨ kv = 2 := by grind
          rcases this with rfl | rfl | rfl
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
          have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by grind
          rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> split_ifs <;> lia
        set j := v - (bd - 3)
        have hj_le : j ≤ 2 := by grind
        set a := (k.val + 3 - j % 3) % 3
        have ha_lt : a < 3 := Nat.mod_lt _ (by grind)
        refine ⟨a, by grind, ?_⟩
        rw [no_wrap a (by grind)]
        have hva : v + a = bd - 3 + (j + a) := by grind
        rw [hva, hc_boundary (j + a) (by grind)]
        have : j = 0 ∨ j = 1 ∨ j = 2 := by grind
        rcases this with h | h | h <;> fin_cases k <;> simp [a, h]
  · push_neg at hwrap
    have hmod_v : v % m = v := Nat.mod_eq_of_lt hv
    have : v = m - 3 ∨ v = m - 2 ∨ v = m - 1 := by grind
    rcases this with hveq | hveq | hveq
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
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
      ((r % 3 + (3 - q % 3)) % 3 + 1) % 3 := by omega

private lemma color_shift_q (r q : ℕ) :
    (r % 3 + (3 - (q + 1) % 3)) % 3 =
      ((r % 3 + (3 - q % 3)) % 3 + 2) % 3 := by omega

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
    have h1 : (3 * (p / (3 * g))) * g = 3 * g * (p / (3 * g)) := by ring
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
  have gk_mod3 : ∀ k a, (g * k + a) % 3 = a % 3 := fun k a => by
    have : 3 * t * k + a = 3 * (t * k) + a := by ring
    rw [ht, this, Nat.mul_add_mod]
  have color_at : ∀ q' r', r' < g → c (g * q' + r') = (r' % 3 + q') % 3 := fun q' r' hr' => by
    simp only [c, gk_mod3, Nat.mul_add_div hg, Nat.div_eq_of_lt hr', add_zero]
  by_cases hr_lt_gm1 : r + 1 < g
  · have hcv : c v = (r % 3 + q) % 3 := hv_eq ▸ color_at q r hr_lt
    have hcvg : c (v + g) = (r % 3 + (q + 1)) % 3 := by
      have : v + g = g * (q + 1) + r := by grind
      rw [this, color_at (q + 1) r hr_lt]
    have hcvg1 : c (v + g + 1) = ((r + 1) % 3 + (q + 1)) % 3 := by
      have : v + g + 1 = g * (q + 1) + (r + 1) := by grind
      rw [this, color_at (q + 1) (r + 1) (by grind)]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g (g + 1)
      (by simp) (by simp) (by simp)
      hcv (by grind)
        (by grind)
  · push_neg at hr_lt_gm1
    have hr_eq : r = g - 1 := by grind
    have hcv : c v = (2 + q) % 3 := by grind
    have hcv1 : c (v + 1) = (q + 1) % 3 := by
      have : v + 1 = g * (q + 1) + 0 := by grind
      rw [this, color_at (q + 1) 0 hg]; grind
    have hcvg : c (v + g) = (2 + (q + 1)) % 3 := by
      have : v + g = g * (q + 1) + (g - 1) := by grind
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
    have hp_eq : p = h * (3 * (p / (3 * h))) + p % (3 * h) := by
      grind [(Nat.mod_add_div p (3 * h)).symm]
    conv_rhs => rw [hp_eq]
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
      have h1 : v + g = h * (q + 1) + (g - 1) := by grind
      have h2 : 3 * t - 1 = 3 * (t - 1) + 2 := by grind
      rw [h1, color_at (q + 1) (g - 1) (by grind), ht, h2]; simp
    have hcv1 : c (v + 1) = (3 - (q + 1) % 3) % 3 := by
      have : v + 1 = h * (q + 1) + 0 := by grind
      rw [this, color_at (q + 1) 0 (by grind)]; grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)
  · have hcv1 : c (v + 1) = ((r + 1) % 3 + (3 - q % 3)) % 3 := by
      have : v + 1 = h * q + (r + 1) := by grind
      rw [this, color_at q (r + 1) (by grind)]
    have hcvg1 : c (v + g + 1) = (r % 3 + (3 - (q + 1) % 3)) % 3 := by
      have : v + g + 1 = h * (q + 1) + r := by grind
      rw [this, color_at (q + 1) r hr_lt]
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
        have hm_lb : m ≥ q * (3 * (g - 1)) + 1 := by grind
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
  have hset : ({0, 1, -(↑g : ZMod m), -(↑g : ZMod m) + 1} : Finset (ZMod m)) =
      (-(↑g : ZMod m)) +ᵥ ({0, 1, (↑g : ZMod m), (↑g : ZMod m) + 1} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add, neg_add_cancel]
    grind
  rw [key, hset]
  exact hasPolychromColouring_vadd

private lemma isUnit_intCast_of_natAbs_coprime {n : ℕ} {b : ℤ}
    (h : Nat.gcd b.natAbs n = 1) :
    IsUnit (Int.cast b : ZMod n) := by
  have hu : IsUnit (b.natAbs : ZMod n) :=
    (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq b with hb | hb
  · have : (Int.cast b : ZMod n) = ↑b.natAbs := by rw [hb]; simp
    rwa [this]
  · have : (Int.cast b : ZMod n) = -↑b.natAbs := by rw [hb]; simp
    rw [this]; exact hu.neg

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
      grind [Finset.card_le_card hsub, Finset.card_le_two (a := (0 : ZMod m)) (b := 1)]
    · have hg'1 : g' = 1 := by rw [← hval, h, Nat.cast_one]
      have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, (1 : ZMod m) + 1} := by
        rw [hg'1]; intro x; simp [Finset.mem_insert, Finset.mem_singleton]
      grind [Finset.card_le_card hsub,
        Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := (1 : ZMod m) + 1)]
  · by_contra hgt; push_neg at hgt
    have hval_lt := ZMod.val_lt g'
    have hgm1 : g'.val = m - 1 := by grind
    have hg'p1 : g' + 1 = 0 := by
      rw [← hval, hgm1, Nat.cast_sub (by grind), Nat.cast_one, ZMod.natCast_self, zero_sub,
        neg_add_cancel]
    have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, g'} := by grind
    grind [Finset.card_le_card hsub,
      Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := g')]
  · conv at hset => rhs; rw [hval.symm]
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
    haveI : Fact (1 < d) := ⟨by grind⟩; simp [ZMod.val_one]
  rw [hival]; split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have := i.val_lt (n := d); grind [Nat.mod_self]

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
  if i.val = d₁ - 1 ∧ ¬Even d₁ then ⟨1 + j.val % 2, by grind⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by grind⟩
  else ⟨2 * (j.val % 2), by grind⟩

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
  simp only [missing_color, zmod_val_add_one d₁ hd₁ i]
  have hi := i.val_lt (n := d₁)
  split_ifs <;> grind [Fin.ext_iff]

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
    (hd₁_ge2 : d₁ ≥ 2)
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

private lemma ZMod.val_add_one {n : ℕ} [NeZero n] (x : ZMod n) :
    (x + 1).val = (x.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

/-- The orbit map φ(i,j) = i*(b-a) + j*b in ZMod m. -/
private def orbitMap (m : ℕ) (a b : ℤ) (d₁ e₁ : ℕ) :
    ZMod d₁ × ZMod e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b

private lemma addOrderOf_b_eq {m : ℕ} {b : ℤ} {d₁ : ℕ} (hm : 0 < m)
    (hd1_def : Nat.gcd b.natAbs m = d₁) :
    addOrderOf (b : ZMod m) = m / d₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = m / d₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (by omega), Nat.gcd_comm, hd1_def]
  rcases Int.natAbs_eq b with h | h
  · rw [show (b : ZMod m) = (b.natAbs : ZMod m) from by rw [h]; simp]; exact key
  · rw [show (b : ZMod m) = -(b.natAbs : ZMod m) from by rw [h]; simp,
        addOrderOf_neg]; exact key

private lemma b_zero_mod_d1 {m : ℕ} {b : ℤ} {d₁ : ℕ}
    (hd1_def : Nat.gcd b.natAbs m = d₁) [NeZero d₁] :
    (b : ZMod d₁) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : d₁ ∣ b.natAbs := hd1_def ▸ Nat.gcd_dvd_left b.natAbs m
  rcases Int.natAbs_eq b with h | h <;> rw [h]
  · exact_mod_cast h1
  · exact dvd_neg.mpr (by exact_mod_cast h1)

private lemma ba_coprime_d1 {m : ℕ} {a b : ℤ} {d₁ : ℕ}
    (hd1_dvd : d₁ ∣ m)
    (h_gcd_coprime : d₁.gcd (Nat.gcd (b - a).natAbs m) = 1) :
    Nat.Coprime (b - a).natAbs d₁ :=
  Nat.dvd_one.mp (h_gcd_coprime ▸
    Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        (dvd_trans (Nat.gcd_dvd_right _ _) hd1_dvd)))

private lemma orbitMap_i_eq {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    {i₁ i₂ : ZMod d₁} {j₁ j₂ : ZMod e₁}
    (heq : orbitMap m a b d₁ e₁ (i₁, j₁) =
           orbitMap m a b d₁ e₁ (i₂, j₂)) :
    i₁ = i₂ := by
  simp only [orbitMap] at heq
  have := congr_arg (ZMod.castHom hd1_dvd (ZMod d₁)) heq
  simp only [map_add, map_mul, map_natCast, map_intCast] at this
  simp only [hb_zero, mul_zero, add_zero, ZMod.natCast_val, ZMod.cast_id] at this
  exact hba_unit.mul_right_cancel this

private lemma orbitMap_j_eq {m : ℕ} {b : ℤ} {e₁ : ℕ} [NeZero e₁]
    (hord : addOrderOf (b : ZMod m) = e₁)
    {j₁ j₂ : ZMod e₁}
    (hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m)) :
    j₁ = j₂ := by
  wlog h : j₁.val ≤ j₂.val with H
  · exact (H hord hj_smul.symm (Nat.le_of_not_le h)).symm
  · have h3 : (j₂.val - j₁.val) • (b : ZMod m) = 0 :=
      add_left_cancel (a := j₁.val • (b : ZMod m))
        (by rw [add_zero, ← add_nsmul, Nat.add_sub_cancel' h]; exact hj_smul.symm)
    have hdvd : e₁ ∣ (j₂.val - j₁.val) := by
      have := addOrderOf_dvd_of_nsmul_eq_zero h3; rwa [hord] at this
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by
      have := j₁.val_lt (n := e₁); have := j₂.val_lt (n := e₁); omega)
    exact ZMod.val_injective _ (by omega)

private lemma orbitMap_injective {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁) :
    Function.Injective (orbitMap m a b d₁ e₁) := by
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
  have hi := orbitMap_i_eq hd1_dvd hb_zero hba_unit heq
  subst hi
  simp only [orbitMap] at heq
  have hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m) := by
    simp only [nsmul_eq_mul]
    exact add_left_cancel heq
  exact Prod.ext rfl (orbitMap_j_eq hord hj_smul)

private lemma orbitMap_bijective {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (hm_eq : m = d₁ * e₁)
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁) :
    Function.Bijective (orbitMap m a b d₁ e₁) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨orbitMap_injective hd1_dvd hb_zero hba_unit hord,
     by simp [Fintype.card_prod, ZMod.card, hm_eq]⟩

private lemma orbitMap_shift_b {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero e₁]
    (he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∀ p : ZMod d₁ × ZMod e₁,
      orbitMap m a b d₁ e₁ p + (b : ZMod m) =
        orbitMap m a b d₁ e₁ (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by
      rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]; push_cast; ring
  · have hje : j.val + 1 = e₁ := by have := j.val_lt (n := e₁); omega
    have hv : (j + 1).val = 0 := by rw [ZMod.val_add_one, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      have : (j.val : ZMod m) * ↑b + ↑b = (j.val + 1 : ℕ) • (b : ZMod m) := by
        rw [add_nsmul, one_nsmul, nsmul_eq_mul]
      rw [this, hje, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]

private lemma orbitMap_shift_ba {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ} [NeZero d₁]
    (i : ZMod d₁) (j : ZMod e₁)
    (hi : i.val + 1 < d₁) :
    orbitMap m a b d₁ e₁ (i, j) + ((b - a : ℤ) : ZMod m) =
      orbitMap m a b d₁ e₁ (i + 1, j) := by
  simp only [orbitMap]
  have : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
  rw [this]; push_cast; ring

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
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd₁_dvd).symm
  have he₁_ge2 : e₁ ≥ 2 := by
    have : 0 < e₁ := Nat.div_pos (Nat.le_of_dvd (by grind) hd₁_dvd)
      (Nat.pos_of_ne_zero (by intro h; simp [h] at h_min)); grind
  haveI : NeZero m := ⟨by grind⟩
  haveI : NeZero d₁ := ⟨by grind⟩
  haveI : NeZero e₁ := ⟨by grind⟩
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := b_zero_mod_d1 rfl
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 hd₁_dvd h_gcd_coprime)
  -- addOrderOf b in ZMod m is e₁
  have hord : addOrderOf (b : ZMod m) = e₁ :=
    addOrderOf_b_eq (by omega) rfl
  have he1_b : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  -- Define the cycle map φ = orbitMap and derive bijectivity from shared infrastructure
  let φ := orbitMap m a b d₁ e₁
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; exact (orbitMap_shift_b he1_b (i, j)).symm
  -- φ is bijective (from shared orbitMap infrastructure)
  let Φ := Equiv.ofBijective φ
    (orbitMap_bijective hm_eq hd₁_dvd hb_zero hba_unit hord)
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
    intro i j; simp only [α, φ, orbitMap]
    rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast, map_intCast,
      hb_zero, mul_zero, add_zero, mul_assoc, ← hu_ba, u_ba.mul_inv, mul_one]
    simp [ZMod.natCast_val]
  -- Φ.symm(x+b) = (same_i, j+1)
  have hΦ_add_b : ∀ x : ZMod m,
      Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := fun x => by
    have key := hφ_add_b (Φ.symm x).1 (Φ.symm x).2
    change Φ ((Φ.symm x).1, (Φ.symm x).2 + 1) = Φ (Φ.symm x) + ↑b at key
    rw [Equiv.apply_symm_apply] at key
    exact Φ.symm_apply_eq.mpr key.symm
  -- (Φ.symm x).1 = α x
  have hΦ_cycle : ∀ x : ZMod m, (Φ.symm x).1 = α x := fun x => by
    have h := hα_φ (Φ.symm x).1 (Φ.symm x).2
    change α (Φ (Φ.symm x)) = _ at h
    rw [Equiv.apply_symm_apply] at h; exact h.symm
  have hd₁_ge2 : d₁ ≥ 2 := by grind
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
  rcases color_covers_even d₁ e₁ hd₁_ge2 hparity i j j' k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  · exact ⟨↑b, by simp, by rw [hχ_nb, h]⟩
  · exact ⟨↑(b - a), by simp, by rw [hχ_nba, h]⟩
  · exact ⟨↑(2 * b - a), by simp, by rw [hχ_n2ba, h]⟩

/-! #### Case (2b): d₁ even, e₁ odd

The coloring assigns each even cycle the pattern `01010…011` and each odd cycle
the pattern `22020…020`. The degenerate pairs `{1,1}` and `{2,2}` occur at
positions `j = e₁ − 2` and `j = 0` respectively; since `e₁ ≥ 3` these positions
are distinct, guaranteeing every 2×2 block contains all three colors.
-/

-- The coloring function for Case 2b.
-- Even cycles: 01010...011 (alternating 0,1, last position overridden to 1)
-- Odd cycles: 22020...020 (first position 2, then: even→0, odd→2)
private def case2b_coloring (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
  if i.val % 2 = 0 then  -- even cycle
    if j.val = e₁ - 1 then 1
    else if j.val % 2 = 0 then 0
    else 1
  else  -- odd cycle
    if j.val = 0 then 2
    else if j.val % 2 = 0 then 0
    else 2

-- Lemma 1: Even cycles never produce color 2.
private lemma case2b_even_ne_two (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 0) :
    case2b_coloring d₁ e₁ (i, j) ≠ 2 := by
  simp only [case2b_coloring, hi, ↓reduceIte]
  split_ifs <;> grind [Fin.ext_iff]

-- Lemma 2: Odd cycles never produce color 1.
private lemma case2b_odd_ne_one (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 1) :
    case2b_coloring d₁ e₁ (i, j) ≠ 1 := by
  simp only [case2b_coloring]
  have : ¬ (i.val % 2 = 0) := by omega
  split_ifs <;> grind [Fin.ext_iff]

-- Lemma 3: Every consecutive pair on an even cycle contains color 1.
private lemma case2b_even_has_one (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 2)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 0) :
    case2b_coloring d₁ e₁ (i, j) = 1 ∨ case2b_coloring d₁ e₁ (i, j + 1) = 1 := by
  simp only [case2b_coloring, hi, ↓reduceIte]
  have hj := j.val_lt (n := e₁)
  have hj1 := zmod_val_add_one e₁ he₁ j
  rw [show (j + 1).val = if j.val + 1 < e₁ then j.val + 1 else 0 from hj1]
  split_ifs <;> (first | left; grind [Fin.ext_iff] | right; grind [Fin.ext_iff])

-- Lemma 4: Every consecutive pair on an odd cycle contains color 2.
private lemma case2b_odd_has_two (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 2)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 1) :
    case2b_coloring d₁ e₁ (i, j) = 2 ∨ case2b_coloring d₁ e₁ (i, j + 1) = 2 := by
  simp only [case2b_coloring]
  have : ¬ (i.val % 2 = 0) := by omega
  have hj := j.val_lt (n := e₁)
  have hj1 := zmod_val_add_one e₁ he₁ j
  rw [show (j + 1).val = if j.val + 1 < e₁ then j.val + 1 else 0 from hj1]
  split_ifs <;> (first | left; grind [Fin.ext_iff] | right; grind [Fin.ext_iff])

-- Lemma 5: Even pair is {1,1} only at j = e₁ − 2.
private lemma case2b_even_degenerate_pos (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 3)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 0)
    (h1 : case2b_coloring d₁ e₁ (i, j) = 1)
    (h2 : case2b_coloring d₁ e₁ (i, j + 1) = 1) :
    j.val = e₁ - 2 := by
  simp only [case2b_coloring, hi, ↓reduceIte] at h1 h2
  have hj := j.val_lt (n := e₁)
  rw [zmod_val_add_one e₁ (by omega) j] at h2
  split_ifs at h1 h2 <;> grind [Fin.ext_iff]

-- Lemma 6: Odd pair is {2,2} only at j = 0. Requires Odd e₁.
private lemma case2b_odd_degenerate_pos (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : Odd e₁) (he₁_ge3 : e₁ ≥ 3)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 1)
    (h1 : case2b_coloring d₁ e₁ (i, j) = 2)
    (h2 : case2b_coloring d₁ e₁ (i, j + 1) = 2) :
    j.val = 0 := by
  simp only [case2b_coloring] at h1 h2
  have hj := j.val_lt (n := e₁)
  obtain ⟨k, hk⟩ := he₁
  rw [zmod_val_add_one e₁ (by omega) j] at h2
  split_ifs at h1 h2 <;> grind

-- Fin 3 helpers for Case 2b.
private lemma case2b_fin3_eq_one {a : Fin 3} (h0 : a ≠ 0) (h2 : a ≠ 2) : a = 1 := by
  fin_cases a <;> simp_all
private lemma case2b_fin3_eq_two {a : Fin 3} (h0 : a ≠ 0) (h1 : a ≠ 1) : a = 2 := by
  fin_cases a <;> simp_all

-- Lemma 9: Coverage — any 2×2 block covers all 3 colors.
-- Generalized for independent j₁, j₂ with compatibility constraints.
-- The compatibility says degenerate positions can't coincide:
-- odd-degenerate at j=0 and even-degenerate at j=e₁-2 are incompatible.
private lemma case2b_coverage_gen (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (hd₁_even : Even d₁) (he₁_odd : Odd e₁) (he₁ : e₁ ≥ 3)
    (i : ZMod d₁) (j₁ j₂ : ZMod e₁)
    (h_compat : j₁.val = 0 → j₂.val ≠ e₁ - 2)
    (h_compat' : j₂.val = 0 → j₁.val ≠ e₁ - 2)
    (k : Fin 3) :
    k = case2b_coloring d₁ e₁ (i, j₁) ∨
    k = case2b_coloring d₁ e₁ (i, j₁ + 1) ∨
    k = case2b_coloring d₁ e₁ (i + 1, j₂) ∨
    k = case2b_coloring d₁ e₁ (i + 1, j₂ + 1) := by
  have he₁_ge2 : e₁ ≥ 2 := by omega
  have hd₁_ge2 : d₁ ≥ 2 := by obtain ⟨k, hk⟩ := hd₁_even; have := NeZero.ne d₁; omega
  have hi_parity := parity_flip_even d₁ hd₁_even hd₁_ge2 i
  rcases Nat.even_or_odd i.val with ⟨_, hi_even⟩ | ⟨_, hi_odd⟩
  · -- i is even, i+1 is odd
    have hi : i.val % 2 = 0 := by omega
    have hi1 : (i + 1).val % 2 = 1 := by omega
    fin_cases k
    · -- k = 0: by contradiction via degenerate position argument
      by_contra h_not
      push_neg at h_not
      have hev1 : case2b_coloring d₁ e₁ (i, j₁) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.1 h.symm)
          (case2b_even_ne_two d₁ e₁ i j₁ hi)
      have hev2 : case2b_coloring d₁ e₁ (i, j₁ + 1) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.2.1 h.symm)
          (case2b_even_ne_two d₁ e₁ i (j₁ + 1) hi)
      have hod1 : case2b_coloring d₁ e₁ (i + 1, j₂) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.2.1 h.symm)
          (case2b_odd_ne_one d₁ e₁ (i + 1) j₂ hi1)
      have hod2 : case2b_coloring d₁ e₁ (i + 1, j₂ + 1) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.2.2 h.symm)
          (case2b_odd_ne_one d₁ e₁ (i + 1) (j₂ + 1) hi1)
      have hj1_eq := case2b_even_degenerate_pos d₁ e₁ he₁ i j₁ hi hev1 hev2
      have hj2_eq := case2b_odd_degenerate_pos d₁ e₁ he₁_odd he₁
        (i + 1) j₂ hi1 hod1 hod2
      exact absurd hj1_eq (h_compat' hj2_eq)
    · -- k = 1: appears in even row
      rcases case2b_even_has_one d₁ e₁ he₁_ge2 i j₁ hi with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
    · -- k = 2: appears in odd row
      rcases case2b_odd_has_two d₁ e₁ he₁_ge2 (i + 1) j₂ hi1 with h | h
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))
  · -- i is odd, i+1 is even
    have hi : i.val % 2 = 1 := by omega
    have hi1 : (i + 1).val % 2 = 0 := by omega
    fin_cases k
    · -- k = 0: by contradiction
      by_contra h_not
      push_neg at h_not
      have hod1 : case2b_coloring d₁ e₁ (i, j₁) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.1 h.symm)
          (case2b_odd_ne_one d₁ e₁ i j₁ hi)
      have hod2 : case2b_coloring d₁ e₁ (i, j₁ + 1) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.1 h.symm)
          (case2b_odd_ne_one d₁ e₁ i (j₁ + 1) hi)
      have hev1 : case2b_coloring d₁ e₁ (i + 1, j₂) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.2.2.1 h.symm)
          (case2b_even_ne_two d₁ e₁ (i + 1) j₂ hi1)
      have hev2 : case2b_coloring d₁ e₁ (i + 1, j₂ + 1) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.2.2.2 h.symm)
          (case2b_even_ne_two d₁ e₁ (i + 1) (j₂ + 1) hi1)
      have hj1_eq := case2b_odd_degenerate_pos d₁ e₁ he₁_odd he₁ i j₁ hi hod1 hod2
      have hj2_eq := case2b_even_degenerate_pos d₁ e₁ he₁ (i + 1) j₂ hi1 hev1 hev2
      exact absurd hj2_eq (h_compat hj1_eq)
    · -- k = 1: appears in even row (i+1)
      rcases case2b_even_has_one d₁ e₁ he₁_ge2 (i + 1) j₂ hi1 with h | h
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))
    · -- k = 2: appears in odd row (i)
      rcases case2b_odd_has_two d₁ e₁ he₁_ge2 i j₁ hi with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)

/-- Subcase (2b): d1 is even and e1 is odd.
    Cycles use modified alternating patterns: even cycles get `01010…011`,
    odd cycles get `22020…020`. -/
lemma case_two_d1_even_e1_odd (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_even : Even (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  set d₁ := Nat.gcd b.natAbs m with hd₁_def
  set e₁ := m / d₁ with he₁_def
  have hd₁_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
  have hd₁_pos : 0 < d₁ := Nat.pos_of_ne_zero (by intro h; simp [h] at h_min)
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd₁_dvd).symm
  -- e₁ ≥ 3: e₁ is odd and e₁ = 1 would give d₁ = m, contradicting gcd(d₁,d₂) = 1
  have he₁_pos : 0 < e₁ :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd₁_dvd) hd₁_pos
  have he₁_ge3 : e₁ ≥ 3 := by
    by_contra h; push_neg at h
    rcases (by omega : e₁ = 1 ∨ e₁ = 2) with he | he
    · have hba_dvd_d₁ : Nat.gcd (b - a).natAbs m ∣ d₁ := by
        rw [hm_eq, he, mul_one]; exact Nat.gcd_dvd_right _ _
      have : Nat.gcd (b - a).natAbs m = 1 :=
        Nat.eq_one_of_dvd_one (h_gcd_coprime ▸ Nat.dvd_gcd hba_dvd_d₁ (dvd_refl _))
      have := h_min; omega
    · obtain ⟨l, hl⟩ := he1_odd; omega
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := b_zero_mod_d1 rfl
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 hd₁_dvd h_gcd_coprime)
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by omega) rfl
  have he1_b : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  -- b/d₁ is coprime to e₁ (needed for compatibility argument)
  have hd₁_dvd_b : (d₁ : ℤ) ∣ b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero
  obtain ⟨q, hq⟩ := hd₁_dvd_b
  have hq_cop : Nat.Coprime q.natAbs e₁ := by
    rw [(by rw [hq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hd₁_pos] :
      q.natAbs = b.natAbs / d₁)]
    exact Nat.coprime_div_gcd_div_gcd hd₁_pos
  -- Define the cycle map φ = orbitMap and derive bijectivity from shared infrastructure
  let φ := orbitMap m a b d₁ e₁
  let Φ := Equiv.ofBijective φ
    (orbitMap_bijective hm_eq hd₁_dvd hb_zero hba_unit hord)
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; exact (orbitMap_shift_b he1_b (i, j)).symm
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
    intro i j; simp only [α, φ, orbitMap]
    rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast, map_intCast,
      hb_zero, mul_zero, add_zero, mul_assoc, ← hu_ba, u_ba.mul_inv, mul_one]
    simp [ZMod.natCast_val]
  -- Φ.symm(x+b) = (same_i, j+1)
  have hΦ_add_b : ∀ x : ZMod m,
      Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := fun x => by
    have key := hφ_add_b (Φ.symm x).1 (Φ.symm x).2
    change Φ ((Φ.symm x).1, (Φ.symm x).2 + 1) = Φ (Φ.symm x) + ↑b at key
    rw [Equiv.apply_symm_apply] at key
    exact Φ.symm_apply_eq.mpr key.symm
  -- (Φ.symm x).1 = α x
  have hΦ_cycle : ∀ x : ZMod m, (Φ.symm x).1 = α x := fun x => by
    have h := hα_φ (Φ.symm x).1 (Φ.symm x).2
    change α (Φ (Φ.symm x)) = _ at h
    rw [Equiv.apply_symm_apply] at h; exact h.symm
  -- d₂ properties for the compatibility argument
  set d₂ := Nat.gcd (b - a).natAbs m
  have hd₂_dvd : d₂ ∣ m := Nat.gcd_dvd_right _ _
  have hd₂_gt1 : d₂ > 1 := by
    have := h_min; simp [d₁, d₂] at this ⊢; omega
  have hd₂_dvd_ba : (d₂ : ℤ) ∣ (b - a) := by
    simpa [Int.gcd, d₂] using Int.gcd_dvd_left (b - a) (m : ℤ)
  have hd₂_dvd_e₁ : d₂ ∣ e₁ := by
    have h1 : d₂ ∣ d₁ * e₁ := hm_eq ▸ hd₂_dvd
    have h2 : Nat.Coprime d₂ d₁ := by rwa [Nat.Coprime, Nat.gcd_comm]
    exact h2.dvd_of_dvd_mul_right (mul_comm d₁ e₁ ▸ h1)
  -- Projection: π(φ(i,j)) = j.val * π(b) since π(b-a) = 0
  haveI : NeZero d₂ := ⟨by omega⟩
  let π : ZMod m → ZMod d₂ := ZMod.castHom hd₂_dvd (ZMod d₂)
  have hπ_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      π (φ (i, j)) = (j.val : ZMod d₂) * π (↑b) := by
    intro i j; simp only [φ, orbitMap, π, map_add, map_mul, map_natCast, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba]; ring
  -- π(b) is a unit in ZMod d₂
  have hπ_b_unit : IsUnit (π (↑b)) := by
    change IsUnit ((ZMod.castHom hd₂_dvd (ZMod d₂)) (↑b))
    rw [map_intCast]
    apply isUnit_intCast_of_natAbs_coprime
    -- gcd(b.natAbs, d₂) = 1: since d₂ coprime to d₁, and b = d₁*q with gcd(q,e₁)=1
    rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left h_gcd_coprime
      (hq_cop.coprime_dvd_right hd₂_dvd_e₁)
  -- Degenerate positions can't coincide: use d₂ | (j-j') from projection
  -- π(n+(b-a)) = π(n) since π(b-a)=0, combined with π(φ(i,j))=j.val*π(b)
  -- gives d₂ | (j.val - j'.val). Then d₂ | e₁ and d₂ > 1, so e₁-2 and 0
  -- can't both be divisible by d₂ (since e₁ odd → gcd(e₁-2, e₁) | 2).
  -- Define coloring and prove polychromaticity
  let χ : ZMod m → Fin 3 := case2b_coloring d₁ e₁ ∘ Φ.symm
  let f := case2b_coloring d₁ e₁
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
  -- Compatibility: degenerate positions don't coincide
  -- Helper: derive False from degenerate-position coincidence
  have h_degenerate_false : ∀ (j₁ j₂ : ZMod e₁),
      (j₁.val : ZMod d₂) * π (↑b) = (j₂.val : ZMod d₂) * π (↑b) →
      j₁.val = 0 → j₂.val = e₁ - 2 → False := by
    intro j₁ j₂ heq hj₁ hj₂
    have hval_eq := hπ_b_unit.mul_right_cancel heq
    rw [hj₁, hj₂, Nat.cast_zero] at hval_eq
    have hd₂_dvd_diff : d₂ ∣ (e₁ - 2) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hval_eq.symm
    have hd₂_dvd_2 : d₂ ∣ 2 := by
      have := Nat.dvd_sub hd₂_dvd_e₁ hd₂_dvd_diff
      rwa [show e₁ - (e₁ - 2) = 2 from by omega] at this
    have hd₂_eq2 : d₂ = 2 := by have := Nat.le_of_dvd (by omega) hd₂_dvd_2; omega
    obtain ⟨k, hk⟩ := hd₂_dvd_e₁; obtain ⟨l, hl⟩ := he1_odd
    rw [hd₂_eq2] at hk; omega
  -- π(n) and π(n+(b-a)) give the same ZMod d₂ value
  have hπ_eq : π (n + ↑(b - a)) = π n := by
    simp only [π, map_add, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba, add_zero]
  have hπn : π n = (j.val : ZMod d₂) * π (↑b) := by
    conv_lhs => rw [show n = Φ p from (Equiv.apply_symm_apply Φ n).symm]
    exact hπ_φ i j
  have hπn' : π n = (j'.val : ZMod d₂) * π (↑b) := by
    rw [← hπ_eq]
    conv_lhs => rw [show n + ↑(b - a) = Φ (Φ.symm (n + ↑(b - a))) from
      (Equiv.apply_symm_apply Φ _).symm]
    exact hπ_φ _ j'
  have hπ_jj' : (j.val : ZMod d₂) * π (↑b) = (j'.val : ZMod d₂) * π (↑b) :=
    hπn.symm.trans hπn'
  have h_compat : j.val = 0 → j'.val ≠ e₁ - 2 := fun hj hj' =>
    h_degenerate_false j j' hπ_jj' hj hj'
  have h_compat' : j'.val = 0 → j.val ≠ e₁ - 2 := fun hj' hj =>
    h_degenerate_false j' j hπ_jj'.symm hj' hj
  rcases case2b_coverage_gen d₁ e₁ hd1_even he1_odd he₁_ge3
      i j j' h_compat h_compat' k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  · exact ⟨↑b, by simp, by rw [hχ_nb, h]⟩
  · exact ⟨↑(b - a), by simp, by rw [hχ_nba, h]⟩
  · exact ⟨↑(2 * b - a), by simp, by rw [hχ_n2ba, h]⟩

-- Pattern assignment for Case 2c, parametrized by k₀ (the wrap shift).
-- Variant A (k₀ % 3 ≠ 2): even→0, odd→1, last→2.
-- Variant B (k₀ % 3 = 2): even→0, odd→2, last→1.
private def case2c_pattern (d₁ k₀ i : ℕ) : Fin 3 :=
  if i = d₁ - 1 ∧ d₁ % 2 = 1 then
    if k₀ % 3 = 2 then 1 else 2
  else if i % 2 = 0 then 0
  else if k₀ % 3 = 2 then 2 else 1

-- Adjacent cycles get different patterns.
private lemma case2c_pattern_ne_succ (d₁ k₀ i : ℕ) (hd₁ : d₁ ≥ 3)
    (hd₁_odd : Odd d₁) (hi : i < d₁) :
    case2c_pattern d₁ k₀ i ≠ case2c_pattern d₁ k₀ ((i + 1) % d₁) := by
  simp only [case2c_pattern]
  obtain ⟨k, hk⟩ := hd₁_odd; subst hk
  have hk03 : k₀ % 3 = 0 ∨ k₀ % 3 = 1 ∨ k₀ % 3 = 2 := by omega
  by_cases hw : i + 1 < 2 * k + 1
  · have hmod := Nat.mod_eq_of_lt hw
    rcases hk03 with h | h | h <;> simp only [h, hmod] <;>
      split_ifs <;> simp [Fin.ext_iff] <;> omega
  · have hi_eq : i = 2 * k := by omega
    have hmod_self : (2 * k + 1) % (2 * k + 1) = 0 := Nat.mod_self _
    simp only [hi_eq, hmod_self]
    split_ifs <;> simp [Fin.ext_iff] <;> omega

-- General coverage: if (j₁ + p₁) % 3 ≠ (j₂ + p₂) % 3, all 3 colors appear.
private lemma cover_mod3_general (p₁ p₂ : Fin 3)
    (j₁ j₂ : ℕ)
    (hne : (j₁ + p₁.val) % 3 ≠ (j₂ + p₂.val) % 3)
    (k : Fin 3) :
    k = ⟨(j₁ + p₁.val) % 3, Nat.mod_lt _ (by omega)⟩ ∨
    k = ⟨(j₁ + 1 + p₁.val) % 3, Nat.mod_lt _ (by omega)⟩ ∨
    k = ⟨(j₂ + p₂.val) % 3, Nat.mod_lt _ (by omega)⟩ ∨
    k = ⟨(j₂ + 1 + p₂.val) % 3, Nat.mod_lt _ (by omega)⟩ := by
  by_contra hall; push_neg at hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  simp [Fin.ext_iff] at h1 h2 h3 h4; omega

-- Non-wrap coverage hypothesis: j₁ = j₂, patterns differ → hypothesis holds.
private lemma case2c_nonwrap_hyp (d₁ k₀ i j : ℕ) (hd₁ : d₁ ≥ 3)
    (hd₁_odd : Odd d₁) (hi : i + 1 < d₁) :
    (j + (case2c_pattern d₁ k₀ i).val) % 3 ≠
    (j + (case2c_pattern d₁ k₀ (i + 1)).val) % 3 := by
  simp only [case2c_pattern]
  obtain ⟨k, hk⟩ := hd₁_odd; subst hk
  split_ifs <;> simp_all <;> omega

-- Wrap coverage hypothesis: j₂ = j₁ + k₀, pattern chosen to avoid conflict.
private lemma case2c_wrap_hyp (d₁ k₀ j : ℕ) (hd₁ : d₁ ≥ 3)
    (hd₁_odd : Odd d₁) :
    (j + (case2c_pattern d₁ k₀ (d₁ - 1)).val) % 3 ≠
    (j + k₀ + (case2c_pattern d₁ k₀ 0).val) % 3 := by
  obtain ⟨k, hk⟩ := hd₁_odd; subst hk
  simp only [case2c_pattern]
  split_ifs <;> simp_all <;> omega

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

private lemma case2d_wrap_shift {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁)
    (hm_eq : m = d₁ * e₁) :
    ∃ k₀ : ZMod e₁,
      (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  have hbij := orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
    set f := ZMod.castHom hd1_dvd (ZMod d₁)
    have hfφ : f (Φ q) = q.1 * ((b - a : ℤ) : ZMod d₁) := by
      change f (orbitMap m a b d₁ e₁ q) = _
      simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast,
        hb_zero, mul_zero, add_zero]
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hφq] at hfφ
    have hf0 : f (d₁ • ((b - a : ℤ) : ZMod m)) = 0 := by
      rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
    rw [hf0] at hfφ
    exact hba_unit.mul_left_eq_zero.mp hfφ.symm
  refine ⟨q.2, ?_⟩
  have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  change orbitMap m a b d₁ e₁ q = _ at hφq
  simp only [orbitMap] at hφq
  rw [show q = (q.1, q.2) from (Prod.eta q).symm] at hφq
  simp only [hq_i, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  simp only [nsmul_eq_mul] at hφq ⊢
  exact hφq.symm

private lemma case2d_shift_ba_wrap {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero e₁] [NeZero d₁]
    (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁)
    (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (i : ZMod d₁) (hi : i.val = d₁ - 1) :
    ∀ (j : ZMod e₁),
      orbitMap m a b d₁ e₁ (i, j) + ((b - a : ℤ) : ZMod m) =
        orbitMap m a b d₁ e₁ (0, j + k₀) := by
  intro j
  simp only [orbitMap, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange i.val*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑i.val : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [hi, ← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑i.val : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j.val * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j.val * ((b : ℤ) : ZMod m) := by
    rw [← hcast]; ring
  rw [step1]
  -- Step 2: d₁*(b-a) = k₀*b via hk₀
  rw [← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul]
  -- Step 3: k₀*b + j*b = (k₀+j)*b, reorder, convert to nsmul
  rw [← add_mul, ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Step 4: reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  have : (j + k₀).val = n % e₁ := by
    rw [ZMod.val_add]
  rw [this]
  conv_lhs => rw [show n = e₁ * (n / e₁) + n % e₁ from (Nat.div_add_mod n e₁).symm]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]

/-- Given d₁ ≥ 3 values each in [u, e₁-u] can sum to any target mod e₁,
    since the range has width ≥ e₁/3 and d₁ ≥ 3. -/
private lemma case2d_rotation_sum_exists {e₁ d₁ : ℕ} [NeZero d₁]
    (hd1_ge : d₁ ≥ 5) (he1_ge : e₁ ≥ 19) (he1_odd : Odd e₁)
    (target : ℕ) :
    ∃ vals : ZMod d₁ → ℕ,
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
  let f : ZMod d₁ → ℕ := fun i =>
    if i.val < q then e₁ - u else if i.val = q then u + r else u
  refine ⟨f, fun i => ?_, ?_⟩
  · change u ≤ f i ∧ f i ≤ e₁ - u
    simp only [f]; split_ifs <;> omega
  · let g : ZMod d₁ → ℕ := fun i =>
      if i.val < q then w else if i.val = q then r else 0
    have hfg : ∀ i : ZMod d₁, f i = u + g i := by
      intro i; simp only [f, g]; split_ifs <;> omega
    have hsum_f : Finset.univ.sum f = d₁ * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, ZMod.card]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have hg_split : ∀ i : ZMod d₁,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by
        intro i; simp only [g]; split_ifs <;> omega
      rw [Finset.sum_congr rfl (fun i _ => hg_split i), Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          smul_eq_mul]
        congr 1
        trans (Finset.image ZMod.val
          (Finset.univ.filter (fun i : ZMod d₁ => i.val < q))).card
        · rw [Finset.card_image_of_injective _ (ZMod.val_injective _)]
        · rw [show Finset.image ZMod.val
              (Finset.univ.filter (fun i : ZMod d₁ => i.val < q)) =
              Finset.range q from by
            ext j; simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
            constructor
            · rintro ⟨i, hi, rfl⟩; exact hi
            · intro hj
              exact ⟨(j : ZMod d₁),
                by rwa [ZMod.val_natCast_of_lt (lt_trans hj hq_lt)],
                ZMod.val_natCast_of_lt (lt_trans hj hq_lt)⟩]
          exact Finset.card_range q
      · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have : (Finset.univ.filter (fun i : ZMod d₁ => i.val = q)).card = 1 := by
          rw [show Finset.univ.filter (fun i : ZMod d₁ => i.val = q) =
              {(q : ZMod d₁)} from by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro h; exact ZMod.val_injective _ (by
                rwa [ZMod.val_natCast_of_lt hq_lt])
            · intro h; rw [h, ZMod.val_natCast_of_lt hq_lt]]
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

/-- Splitting a ZMod filter sum at a boundary -/
private lemma zmod_filter_sum_succ {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1)).sum f =
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i := by
  have hsplit : Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1) =
      Finset.univ.filter (fun k : ZMod n => k.val < i.val) ∪ {i} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hk; by_cases hk' : k.val < i.val
      · left; exact hk'
      · right; exact ZMod.val_injective _ (by omega)
    · rintro (hk | hk)
      · omega
      · rw [hk]; omega
  rw [hsplit, Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; intro k hk hk'; rw [hk'] at hk; omega),
    Finset.sum_singleton]

/-- When i is the max element, {k | k < i} ∪ {i} = univ. -/
private lemma zmod_filter_sum_last {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n)
    (hi : i.val = n - 1) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by
  rw [← zmod_filter_sum_succ f i]; congr 1; ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ => True.intro, fun _ => by have := k.val_lt (n := n); omega⟩

-- Position arithmetic helpers for case2d_coloring_works

/-- Position shift by 1: adding 1 to ZMod coordinate shifts position by 1 mod n. -/
private lemma pos_shift_one {n : ℕ} [NeZero n] (j : ZMod n) (c : ℕ) :
    ((j + 1).val + c) % n = ((j.val + c) % n + 1) % n := by
  rw [ZMod.val_add_one, Nat.mod_add_mod, Nat.mod_add_mod]; congr 1; omega

/-- (j + (S + V) % n) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_succ' (j S V n : ℕ) :
    (j + (S + V) % n) % n = ((j + S % n) % n + V) % n := by
  rw [Nat.add_mod_mod, show j + (S + V) = j + S + V from by omega,
      ← Nat.mod_add_mod (j + S) n V,
      show (j + S) % n = (j + S % n) % n from (Nat.add_mod_mod j S n).symm]

/-- Wrap case: if (S + V) % n = k₀ % n, then
    (j + k₀) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_wrap' (j S V k₀ n : ℕ)
    (hsum : (S + V) % n = k₀ % n) :
    (j + k₀) % n = ((j + S % n) % n + V) % n := by
  rw [← Nat.add_mod_mod j k₀ n, ← hsum, pos_shift_succ']

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
  have he1_pos : 0 < e₁ := by omega
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd1_dvd).symm
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by omega) hd1_def
  have hb_zero : (b : ZMod d₁) = 0 := b_zero_mod_d1 hd1_def
  have hba_coprime := ba_coprime_d1 hd1_dvd (by rwa [hd1_def])
  have hba_unit := isUnit_intCast_of_natAbs_coprime hba_coprime
  have he1_b_zero : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  have hbij := orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hd1_dvd hb_zero hba_unit hord hm_eq
  -- d₁ is odd, > 1, and ¬(3∣d₁), so d₁ ≥ 5
  have hd1_ge5 : d₁ ≥ 5 := by
    have : d₁ > 1 := by omega
    obtain ⟨k, hk⟩ := hd1_odd; omega
  obtain ⟨vals, hvals_bound, hvals_sum⟩ :=
    case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
  -- Cumulative rotation: rot(i) = (Σ_{j<i} vals(j)) % e₁
  let rot : ZMod d₁ → ℕ := fun i =>
    ((Finset.univ.filter (fun j : ZMod d₁ => j.val < i.val)).sum vals) % e₁
  -- Coloring: χ(x) = basePattern(e₁, (j-coord + rot(i-coord)) % e₁)
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    basePattern e₁ ((coord.2.val + rot coord.1) % e₁)
  refine ⟨χ, fun n k => ?_⟩
  -- χ at orbit coordinates simplifies via Equiv.symm_apply_apply
  have hχ_eq : ∀ (i' : ZMod d₁) (j' : ZMod e₁),
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
    rw [← hn, hij]; exact (orbitMap_shift_b he1_b_zero (i, j)).symm
  -- Apply rotation covers
  have covers := basePattern_rotation_covers he1_odd he1_ge
    (hvals_bound i).1 (hvals_bound i).2 hp_lt k
  simp only [Finset.mem_insert, Finset.mem_singleton] at covers
  -- (b-a) shift: obtain shifted coordinates and position equality
  suffices ∃ (i_new : ZMod d₁) (j_new : ZMod e₁),
      Φ (i_new, j_new) = n + ((b - a : ℤ) : ZMod m) ∧
      (j_new.val + rot i_new) % e₁ = (p + vals i) % e₁ by
    obtain ⟨i_new, j_new, hΦ_ba, hpos⟩ := this
    have hΦ_2ba : Φ (i_new, j_new + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      have : ((2 * b - a : ℤ) : ZMod m) =
          ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by
        push_cast; ring
      rw [this, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (i_new, j_new)).symm
    rcases covers with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b, by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · exact ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b,
        by rw [← hΦ_b, hχ_eq, h]; congr 1; exact pos_shift_one j (rot i)⟩
    · exact ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b,
        by rw [← hΦ_ba, hχ_eq, h]; congr 1⟩
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      calc ((j_new + 1 : ZMod e₁).val + rot i_new) % e₁
          = ((j_new.val + rot i_new) % e₁ + 1) % e₁ :=
            pos_shift_one j_new (rot i_new)
        _ = ((p + vals i) % e₁ + 1) % e₁ := by rw [hpos]
        _ = (p + vals i + 1) % e₁ := Nat.mod_add_mod (p + vals i) e₁ 1
  by_cases hi : i.val + 1 < d₁
  · -- No-wrap case
    refine ⟨i + 1, j, ?_, ?_⟩
    · rw [← hn, hij]; exact (orbitMap_shift_ba i j hi).symm
    · change (j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < (i + 1).val)).sum vals) % e₁) % e₁ =
        ((j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
      have : (i + 1).val = i.val + 1 := by
        rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      rw [this, zmod_filter_sum_succ vals i]
      exact pos_shift_succ' j.val _ (vals i) e₁
  · -- Wrap case: i = d₁ - 1
    have hi_eq : i.val = d₁ - 1 := by
      have := i.val_lt (n := d₁); omega
    refine ⟨0, j + k₀, ?_, ?_⟩
    · rw [← hn, hij]; exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    · have hrot0 : rot (0 : ZMod d₁) = 0 := by simp [rot, ZMod.val_zero]
      have htotal :
          (Finset.univ.filter (fun k : ZMod d₁ => k.val < i.val)).sum vals +
            vals i = Finset.univ.sum vals :=
        zmod_filter_sum_last vals i hi_eq
      rw [hrot0, Nat.add_zero, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁ (by rw [htotal, hvals_sum])

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

-- Mod 3 arithmetic: (a % e₁ + b) % 3 = (a + b) % 3 when 3 ∣ e₁
private lemma case2c_mod3 {e₁ : ℕ} (h3e : 3 ∣ e₁) (x y : ℕ) :
    (x % e₁ + y) % 3 = (x + y) % 3 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd x h3e, ← Nat.add_mod]

/-- Subcase (2c): d₁ and e₁ are both odd, with e₁ ≤ 17 and 3 ∣ e₁.
    Each cycle Cᵢ is colored with one of three shifted 012-patterns:
      Pattern p: position j gets color (j + p) mod 3.
    Adjacent cycles use different patterns, ensuring all 2×2 blocks
    (translates of S) contain all 3 colors. -/
lemma case_two_odd_small (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_odd : Odd (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m))
    (he1_le : m / Nat.gcd b.natAbs m ≤ 17)
    (he1_div3 : 3 ∣ m / Nat.gcd b.natAbs m) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  set d₁ := Nat.gcd b.natAbs m with hd1_def
  set e₁ := m / d₁ with he1_def
  have hd1_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
  have hd1_gt1 : d₁ > 1 := by omega
  have he1_ge3 : e₁ ≥ 3 := by
    obtain ⟨k, hk⟩ := he1_div3; obtain ⟨j, hj⟩ := he1_odd; omega
  have he1_pos : 0 < e₁ := by omega
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd1_dvd).symm
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero d₁ := ⟨by omega⟩
  haveI : NeZero e₁ := ⟨by omega⟩
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by omega) hd1_def
  have hb_zero : (b : ZMod d₁) = 0 := b_zero_mod_d1 hd1_def
  have hba_coprime := ba_coprime_d1 hd1_dvd (by rwa [hd1_def])
  have hba_unit := isUnit_intCast_of_natAbs_coprime hba_coprime
  have he1_b_zero : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  have hbij := orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hd1_dvd hb_zero hba_unit hord hm_eq
  have hd1_ge3 : d₁ ≥ 3 := by obtain ⟨k, hk⟩ := hd1_odd; omega
  -- Coloring: χ(x) = (j + pattern(i)) mod 3 where (i,j) = Φ⁻¹(x)
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    ⟨(coord.2.val + (case2c_pattern d₁ k₀.val coord.1.val).val) % 3,
     Nat.mod_lt _ (by omega)⟩
  refine ⟨χ, fun n k => ?_⟩
  -- χ at orbit coordinates
  have hχ_eq : ∀ (i' : ZMod d₁) (j' : ZMod e₁),
      χ (Φ (i', j')) = ⟨(j'.val + (case2c_pattern d₁ k₀.val i'.val).val) % 3,
        Nat.mod_lt _ (by omega)⟩ := by
    intro i' j'; simp only [χ, Equiv.symm_apply_apply]
  -- Coordinates of n
  set ij := Φ.symm n with hij_def
  have hn : Φ ij = n := Equiv.apply_symm_apply Φ n
  set i := ij.1 with hi_def
  set j := ij.2 with hj_def
  have hij : ij = (i, j) := (Prod.eta ij).symm
  set p := case2c_pattern d₁ k₀.val i.val
  -- ZMod e₁ successor: (jj + 1).val = (jj.val + 1) % e₁
  have hzmod_succ : ∀ (jj : ZMod e₁),
      (jj + 1 : ZMod e₁).val = (jj.val + 1) % e₁ := fun jj => ZMod.val_add_one jj
  -- Shift: n + b = Φ(i, j+1)
  have hΦ_b : Φ (i, j + 1) = n + ((b : ℤ) : ZMod m) := by
    rw [← hn, hij]; exact (orbitMap_shift_b he1_b_zero (i, j)).symm
  -- Case split: wrap or non-wrap
  by_cases hi : i.val + 1 < d₁
  · -- Non-wrap case: i+1 < d₁
    set i' := i + 1
    set p' := case2c_pattern d₁ k₀.val i'.val
    -- Shift: n + (b-a) = Φ(i', j)
    have hΦ_ba : Φ (i', j) = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]; exact (orbitMap_shift_ba i j hi).symm
    -- Shift: n + (2b-a) = Φ(i', j+1)
    have hΦ_2ba : Φ (i', j + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      have : ((2 * b - a : ℤ) : ZMod m) =
          ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by push_cast; ring
      rw [this, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (i', j)).symm
    -- Coverage hypothesis
    have hi'_eq : i'.val = i.val + 1 := by
      rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
    have hhyp : (j.val + p.val) % 3 ≠ (j.val + p'.val) % 3 := by
      change (j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3 ≠
        (j.val + (case2c_pattern d₁ k₀.val i'.val).val) % 3
      rw [hi'_eq]
      exact case2c_nonwrap_hyp d₁ k₀.val i.val j.val hd1_ge3 hd1_odd hi
    -- Apply cover_mod3_general
    rcases cover_mod3_general p p' j.val j.val hhyp k with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b,
        by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · refine ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_b, hχ_eq, h]; congr 1
      rw [hzmod_succ, case2c_mod3 he1_div3]
    · exact ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b,
        by rw [← hΦ_ba, hχ_eq, h]⟩
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      rw [hzmod_succ, case2c_mod3 he1_div3]
  · -- Wrap case: i = d₁ - 1
    have hi_eq : i.val = d₁ - 1 := by
      have := i.val_lt (n := d₁); omega
    set j' : ZMod e₁ := j + k₀
    set p₀ := case2c_pattern d₁ k₀.val 0
    -- Shift: n + (b-a) = Φ(0, j')
    have hΦ_ba : Φ (0, j') = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]
      exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    -- Shift: n + (2b-a) = Φ(0, j'+1)
    have hΦ_2ba : Φ (0, j' + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      have : ((2 * b - a : ℤ) : ZMod m) =
          ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by push_cast; ring
      rw [this, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (0, j')).symm
    -- Coverage hypothesis: (j + p_last) % 3 ≠ (j + k₀ + p₀) % 3
    have hp_eq : p = case2c_pattern d₁ k₀.val (d₁ - 1) := by
      change case2c_pattern d₁ k₀.val i.val = _; rw [hi_eq]
    have hhyp : (j.val + p.val) % 3 ≠ (j.val + k₀.val + p₀.val) % 3 := by
      rw [hp_eq]; exact case2c_wrap_hyp d₁ k₀.val j.val hd1_ge3 hd1_odd
    -- Apply cover_mod3_general
    rcases cover_mod3_general p p₀ j.val (j.val + k₀.val) hhyp k
      with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b,
        by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · refine ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_b, hχ_eq, h]; congr 1
      rw [hzmod_succ, case2c_mod3 he1_div3]
    · refine ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_ba, hχ_eq, h]; congr 1
      change (j'.val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 =
        (j.val + k₀.val + p₀.val) % 3
      rw [ZMod.val_zero, show j'.val = (j.val + k₀.val) % e₁ from ZMod.val_add j k₀]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) p₀.val
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      change ((j' + 1).val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 =
        (j.val + k₀.val + 1 + p₀.val) % 3
      rw [ZMod.val_zero, hzmod_succ,
          show j'.val = (j.val + k₀.val) % e₁ from ZMod.val_add j k₀]
      rw [case2c_mod3 he1_div3 ((j.val + k₀.val) % e₁ + 1) p₀.val]
      rw [show (j.val + k₀.val) % e₁ + 1 + p₀.val =
            (j.val + k₀.val) % e₁ + (1 + p₀.val) by omega,
          show j.val + k₀.val + 1 + p₀.val =
            j.val + k₀.val + (1 + p₀.val) by omega]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) (1 + p₀.val)

/-- When gcd(d₁,d₂) = 1, both d₁,d₂ > 1, both d₁,d₂ divide m,
    and m/d₁ ≤ 17 and m/d₂ ≤ 17, we get m ≤ 289. Combined with
    m ≥ 289 this forces m = 289 = 17², but then gcd(d₁,d₂) = 1 with
    d₁,d₂ | 17² and d₁,d₂ > 1 is impossible. -/
private lemma no_both_e_small {m d₁ d₂ : ℕ}
    (hm : m ≥ 289)
    (hcop : Nat.gcd d₁ d₂ = 1)
    (hd₁_gt1 : d₁ > 1) (hd₂_gt1 : d₂ > 1)
    (hd₁_dvd : d₁ ∣ m) (hd₂_dvd : d₂ ∣ m)
    (he₁_le : m / d₁ ≤ 17) (he₂_le : m / d₂ ≤ 17) : False := by
  have hd₁_bound : m ≤ d₁ * 17 := by
    calc m = d₁ * (m / d₁) := (Nat.mul_div_cancel' hd₁_dvd).symm
      _ ≤ d₁ * 17 := Nat.mul_le_mul_left d₁ he₁_le
  have hd₂_bound : m ≤ d₂ * 17 := by
    calc m = d₂ * (m / d₂) := (Nat.mul_div_cancel' hd₂_dvd).symm
      _ ≤ d₂ * 17 := Nat.mul_le_mul_left d₂ he₂_le
  have hprod_le : d₁ * d₂ ≤ m :=
    Nat.le_of_dvd (by omega)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by rwa [Nat.Coprime]) hd₁_dvd hd₂_dvd)
  -- d₁*d₂ ≤ m ≤ d₁*17 → d₂ ≤ 17; similarly d₁ ≤ 17
  have hd₂_le : d₂ ≤ 17 :=
    Nat.le_of_mul_le_mul_left (hprod_le.trans hd₁_bound) (by omega)
  have hd₁_le : d₁ ≤ 17 := by
    have : d₁ * d₂ ≤ d₂ * 17 := hprod_le.trans hd₂_bound
    rw [mul_comm d₁ d₂] at this
    exact Nat.le_of_mul_le_mul_left this (by omega)
  -- 289 ≤ m ≤ d₁*17 → d₁ ≥ 17; similarly d₂ ≥ 17
  -- So d₁ = d₂ = 17, gcd(17,17) = 17 ≠ 1.
  have hd₁_eq : d₁ = 17 := by omega
  have hd₂_eq : d₂ = 17 := by omega
  rw [hd₁_eq, hd₂_eq] at hcop; simp at hcop

/-- Aggregation of Main Case 2.
    Assumption: min(gcd(b, m), gcd(b-a, m)) > 1.
    Matches the paper's proof structure: first WLOG swap so that 3 ∤ d₁
    (choosing the smallest non-multiple-of-3), then split into subcases
    (2a)–(2d). -/
lemma main_case_two (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  rcases Nat.even_or_odd (m / Nat.gcd b.natAbs m) with he | ho
  · exact case_two_e1_even m a b hm h_gcd_coprime h_min he
  · rcases Nat.even_or_odd (Nat.gcd b.natAbs m) with hd | hd
    · exact case_two_d1_even_e1_odd m a b hm h_gcd_coprime h_min hd ho
    · -- Both d₁ and e₁ odd.
      -- Paper: "Choose the smallest of d₁,d₂ not a multiple of 3, WLOG d₁."
      -- Swap if 3 ∣ d₁, then dispatch with 3 ∤ d₁.
      suffices dispatch : ∀ (a' b' : ℤ),
          (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 →
          min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 →
          Odd (Nat.gcd b'.natAbs m) →
          Odd (m / Nat.gcd b'.natAbs m) →
          ¬ (3 ∣ Nat.gcd b'.natAbs m) →
          HasPolychromColouring (Fin 3) (zmod_set m a' b') by
        by_cases h3 : 3 ∣ Nat.gcd b.natAbs m
        · -- Swap roles of b and b-a
          rw [← zmod_set_swap m a b]
          set a' := (-a : ℤ); set b' := (b - a : ℤ)
          have hba_eq : (b' - a').natAbs = b.natAbs := by
            change (b - a - -a).natAbs = b.natAbs; congr 1; ring
          have hcop' : (Nat.gcd b'.natAbs m).gcd
              (Nat.gcd (b' - a').natAbs m) = 1 := by
            rw [hba_eq]; rwa [Nat.gcd_comm]
          have hmin' : min (Nat.gcd b'.natAbs m)
              (Nat.gcd (b' - a').natAbs m) > 1 := by
            rw [hba_eq]; rwa [min_comm]
          have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
            intro h3d'; have := Nat.dvd_gcd h3 h3d'
            rw [h_gcd_coprime] at this; omega
          rcases Nat.even_or_odd (m / Nat.gcd b'.natAbs m) with he' | ho'
          · exact case_two_e1_even m a' b' hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b'.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd m a' b' hm hcop' hmin' hd' ho'
            · exact dispatch a' b' hcop' hmin' hd' ho' h3'
        · exact dispatch a b h_gcd_coprime h_min hd ho h3
      -- Prove dispatch: given ¬(3 ∣ d₁), split on e₁ size
      intro a' b' hcop hmin hd₁_odd he₁_odd h3_nd₁
      set d₁ := Nat.gcd b'.natAbs m
      set d₂ := Nat.gcd (b' - a').natAbs m
      set e₁ := m / d₁
      have hd₁_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
      have hd₂_dvd : d₂ ∣ m := Nat.gcd_dvd_right _ _
      have hd₂_pos : 0 < d₂ :=
        Nat.pos_of_ne_zero (by intro h; simp [h] at hmin)
      by_cases he_le : e₁ ≤ 17
      · -- Case 2c: prove 3 ∣ e₁
        -- Since gcd(d₁,d₂)=1 and 3 ∤ d₁, if 3 ∣ d₂ then 3 ∣ m hence 3 ∣ e₁.
        -- If 3 ∤ d₂: swap and show e₂ ≥ 19 (contradiction with both ≤ 17).
        by_cases h3d₂ : 3 ∣ d₂
        · have h3m : 3 ∣ m := dvd_trans h3d₂ hd₂_dvd
          have h3e₁ : 3 ∣ e₁ := by
            have h3de : 3 ∣ d₁ * e₁ :=
              (Nat.mul_div_cancel' hd₁_dvd).symm ▸ h3m
            have hcop3 : Nat.Coprime 3 d₁ :=
              (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3_nd₁
            exact hcop3.dvd_of_dvd_mul_left h3de
          exact case_two_odd_small m a' b' hm hcop hmin hd₁_odd he₁_odd
            he_le h3e₁
        · -- 3 ∤ d₁ and 3 ∤ d₂ and e₁ ≤ 17: swap and show new e₁ ≥ 19.
          -- After swap, new e₁' = m/d₂. If e₁' ≤ 17 too, contradiction.
          rw [← zmod_set_swap m a' b']
          set a'' := (-a' : ℤ); set b'' := (b' - a' : ℤ)
          have hba_eq : (b'' - a'').natAbs = b'.natAbs := by
            change (b' - a' - -a').natAbs = b'.natAbs; congr 1; ring
          have hcop' : (Nat.gcd b''.natAbs m).gcd
              (Nat.gcd (b'' - a'').natAbs m) = 1 := by
            rw [hba_eq]; rwa [Nat.gcd_comm]
          have hmin' : min (Nat.gcd b''.natAbs m)
              (Nat.gcd (b'' - a'').natAbs m) > 1 := by
            rw [hba_eq]; rwa [min_comm]
          -- Dispatch on parity
          rcases Nat.even_or_odd (m / Nat.gcd b''.natAbs m) with he' | ho'
          · exact case_two_e1_even m a'' b'' hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b''.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd m a'' b'' hm hcop' hmin' hd' ho'
            · -- Both odd after swap. Show e₁' ≥ 19 by contradiction.
              have he₁'_ge : m / Nat.gcd b''.natAbs m ≥ 19 := by
                by_contra hlt; push_neg at hlt
                have hle : m / Nat.gcd b''.natAbs m ≤ 17 := by
                  obtain ⟨k', hk'⟩ := ho'; omega
                have hd₁_gt1 : d₁ > 1 := by omega
                have hd₂_gt1 : d₂ > 1 := by omega
                rw [Nat.gcd_comm] at hcop
                exact no_both_e_small hm hcop hd₂_gt1 hd₁_gt1
                  hd₂_dvd hd₁_dvd hle he_le
              exact case_two_odd_large m a'' b'' hm hcop' hmin' hd' ho'
                he₁'_ge h3d₂
      · have he₁_ge : e₁ ≥ 19 := by
          obtain ⟨k, hk⟩ := he₁_odd; omega
        exact case_two_odd_large m a' b' hm hcop hmin hd₁_odd he₁_odd
          he₁_ge h3_nd₁

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
      (x : ZMod m) ≠ (y : ZMod m) := fun _ _ hx1 hx2 hy1 hy2 hxy h =>
    hxy (by rwa [ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hx1 hx2,
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
  -- d divides b, (b-a), and m (lifted to ℤ)
  have hd_b : (d : ℤ) ∣ b := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_left _ _))
  have hd_m : (d : ℤ) ∣ ↑m := Int.natCast_dvd_natCast.mpr
    ((Nat.gcd_dvd_left _ (Nat.gcd _ _)).trans (Nat.gcd_dvd_right _ _))
  have hd_ba : (d : ℤ) ∣ (b - a) := Int.natCast_dvd.mpr
    ((Nat.gcd_dvd_right (Nat.gcd _ _) _).trans (Nat.gcd_dvd_left _ _))
  -- d | a and d | c follow from d | b, d | (b-a), d | m
  have hd_a : (d : ℤ) ∣ a := (by ring : a = b - (b - a)) ▸ dvd_sub hd_b hd_ba
  have hd_c : (d : ℤ) ∣ c := (by grind : (c : ℤ) = ↑m - b + a) ▸
    dvd_add (dvd_sub hd_m hd_b) hd_a
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
  have hm_eq : (m : ℤ) = c - a + b := Int.toNat_of_nonneg (by grind)
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
