import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-! Test file for idx_in_interval -/

open Finpartition in
/-- idx(p) satisfies equiEndpoint bounds. -/
lemma idx_in_interval (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1) else r + (p - bd) / q
    j < s ∧
    equiEndpoint m s j ≤ p ∧
    p < equiEndpoint m s (j + 1) := by
  simp only
  set q := m / s; set r := m % s; set bd := r * (q + 1)
  have hq_pos : 0 < q := Nat.div_pos hs_le hs
  have hr_lt : r < s := Nat.mod_lt m hs
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hbd_le_m : bd + (s - r) * q = m := by
    have : (s - r) * q + r * q = s * q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
    have : bd = r * q + r := by ring
    linarith
  split
  · -- Case p < bd: j = p / (q + 1)
    rename_i hlt
    set j := p / (q + 1)
    have hq1_pos : 0 < q + 1 := by omega
    have hj_lt_r : j < r := by
      rw [Nat.div_lt_iff_lt_mul hq1_pos]; exact hlt
    have hdam : (q + 1) * j + p % (q + 1) = p :=
      Nat.div_add_mod p (q + 1)
    have hmod : p % (q + 1) < q + 1 := Nat.mod_lt p hq1_pos
    -- Ring identities bridging product forms
    have hr1 : (q + 1) * j = q * j + j := by ring
    have hr2 : (q + 1) * j + (q + 1) = q * (j + 1) + (j + 1) :=
      by ring
    -- Lower: q*j + j ≤ p
    have hle : q * j + j ≤ p := by linarith
    -- Upper: p < q*(j+1) + (j+1)
    have hub : p < q * (j + 1) + (j + 1) := by linarith
    refine ⟨by omega, ?_, ?_⟩
    · unfold equiEndpoint
      rw [min_eq_right (by omega : j ≤ r)]
      change q * j + j ≤ p; exact hle
    · unfold equiEndpoint
      rw [min_eq_right (by omega : j + 1 ≤ r)]
      change p < q * (j + 1) + (j + 1); exact hub
  · -- Case p ≥ bd: j = r + (p - bd) / q
    rename_i hge; push_neg at hge
    set d := (p - bd) / q
    have hdam : q * d + (p - bd) % q = p - bd :=
      Nat.div_add_mod (p - bd) q
    have hmod : (p - bd) % q < q := Nat.mod_lt _ hq_pos
    -- Lower and upper for d: q*d ≤ p-bd < q*(d+1)
    have hqd_le : q * d ≤ p - bd := by linarith
    have hqd_ub : p - bd < q * d + q := by linarith
    have hd_lt : d < s - r := by
      -- p - bd < (s-r)*q (since p < m = bd + (s-r)*q)
      -- q*d ≤ p - bd < (s-r)*q
      -- q*d < (s-r)*q → d < s-r (since q > 0)
      rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
    set j := r + d
    -- Bridge: q*j + r = bd + q*d (relates equiEndpoint to bd+offset)
    have hring_j : q * j + r = bd + q * d := by
      have : q * j = q * r + q * d := by ring
      have : bd = r * q + r := by ring
      linarith
    have hring_j1 : q * (j + 1) + r = bd + q * d + q := by
      have : q * (j + 1) = q * r + q * d + q := by ring
      have : bd = r * q + r := by ring
      linarith
    -- Lower: q*j + r ≤ p
    have hle : q * j + r ≤ p := by linarith
    -- Upper: p < q*(j+1) + r
    have hub : p < q * (j + 1) + r := by linarith
    refine ⟨by omega, ?_, ?_⟩
    · unfold equiEndpoint
      rw [min_eq_left (by omega : r ≤ j)]
      change q * j + r ≤ p; exact hle
    · unfold equiEndpoint
      rw [min_eq_left (by omega : r ≤ j + 1)]
      change p < q * (j + 1) + r; exact hub
