import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Scratch file 3: gap bound proof

Prove that idx((v+g)%m) differs from idx(v) by 1 or 2 mod s.
-/

open Finpartition in
/-- idx(p) satisfies equiEndpoint(m,s,j) ≤ p < equiEndpoint(m,s,j+1)
    and j < s. -/
lemma idx_in_interval (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1)
      else r + (p - bd) / q
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
    have hmod : p % (q + 1) < q + 1 :=
      Nat.mod_lt p hq1_pos
    have hr1 : (q + 1) * j = q * j + j := by ring
    have hr2 : (q + 1) * j + (q + 1) =
        q * (j + 1) + (j + 1) := by ring
    have hle : q * j + j ≤ p := by omega
    have hub : p < q * (j + 1) + (j + 1) := by omega
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
    have hmod : (p - bd) % q < q :=
      Nat.mod_lt _ hq_pos
    have hqd_le : q * d ≤ p - bd := by omega
    have hqd_ub : p - bd < q * d + q := by omega
    have hd_lt : d < s - r := by
      rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
    set j := r + d
    have hring_j : q * j + r = bd + q * d := by
      have : q * j = q * r + q * d := by ring
      have : bd = r * q + r := by ring
      linarith
    have hring_j1 :
        q * (j + 1) + r = bd + q * d + q := by
      have : q * (j + 1) = q * r + q * d + q := by
        ring
      have : bd = r * q + r := by ring
      linarith
    have hle : q * j + r ≤ p := by omega
    have hub : p < q * (j + 1) + r := by omega
    have hr_le_j : r ≤ j := Nat.le_add_right r d
    have hr_le_j1 : r ≤ j + 1 := Nat.le_succ_of_le hr_le_j
    refine ⟨by omega, ?_, ?_⟩
    · unfold equiEndpoint
      rw [min_eq_left hr_le_j]
      change q * j + r ≤ p; exact hle
    · unfold equiEndpoint
      rw [min_eq_left hr_le_j1]
      change p < q * (j + 1) + r; exact hub

/-- The interval length: q+1 for the first r intervals, q for the rest. -/
lemma equiEndpoint_diff (m s j : ℕ) :
    Finpartition.equiEndpoint m s (j + 1) -
      Finpartition.equiEndpoint m s j =
      if j < m % s then m / s + 1 else m / s :=
  Finpartition.card_of_mem_equipartitionToIco_parts_aux

open Finpartition in
/-- g exceeds every interval length. -/
lemma gap_exceeds_ilen (m s g : ℕ) (hs : 0 < s)
    (h_lb : (m + s - 1) / s < g) (j : ℕ) :
    equiEndpoint m s (j + 1) - equiEndpoint m s j < g := by
  rw [equiEndpoint_diff]
  set q := m / s; set r := m % s
  by_cases hr : j < r
  · simp [hr]
    have hr_pos : 0 < r := by omega
    have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
    have : (q + 1) * s = s * q + s := by ring
    have : (q + 1) * s ≤ m + s - 1 := by omega
    have := Nat.le_div_iff_mul_le hs |>.mpr this
    omega
  · simp [hr]
    have : q * s ≤ m := Nat.div_mul_le_self m s
    have : q * s ≤ m + s - 1 := by omega
    have := Nat.le_div_iff_mul_le hs |>.mpr this
    omega

open Finpartition in
/-- If p is in interval j (equiEndpoint(j) ≤ p < equiEndpoint(j+1)),
    then p + g ≥ equiEndpoint(j+1). -/
lemma shift_past_interval (m s g : ℕ) (hs : 0 < s)
    (h_lb : (m + s - 1) / s < g)
    (j p : ℕ) (hlo : equiEndpoint m s j ≤ p)
    (hhi : p < equiEndpoint m s (j + 1)) :
    equiEndpoint m s (j + 1) ≤ p + g := by
  have := gap_exceeds_ilen m s g hs h_lb j
  omega

open Finpartition in
/-- g < 2 * (every interval length). -/
lemma gap_lt_twice_ilen (m s g : ℕ)
    (h_ub : g < 2 * (m / s)) (j : ℕ) :
    g < 2 * (equiEndpoint m s (j + 1) - equiEndpoint m s j) := by
  rw [equiEndpoint_diff]; split <;> omega

open Finpartition in
/-- p + g < equiEndpoint(j+3) when p < equiEndpoint(j+1) and g < 2q. -/
lemma shift_within_two (m s g : ℕ)
    (h_ub : g < 2 * (m / s))
    (j p : ℕ) (hhi : p < equiEndpoint m s (j + 1)) :
    p + g < equiEndpoint m s (j + 3) := by
  have hm1 : equiEndpoint m s (j + 2) - equiEndpoint m s (j + 1) ≥ m / s := by
    rw [equiEndpoint_diff]; split <;> omega
  have hm2 : equiEndpoint m s (j + 3) - equiEndpoint m s (j + 2) ≥ m / s := by
    rw [equiEndpoint_diff]; split <;> omega
  have hmono : equiEndpoint m s (j + 1) ≤ equiEndpoint m s (j + 2) :=
    equiEndpoint_monotone (by omega)
  omega

open Finpartition in
/-- If equiEndpoint(a) ≤ p and p < equiEndpoint(b), and idx(p) has
    equiEndpoint(idx) ≤ p < equiEndpoint(idx+1), then a ≤ idx < b.
    This follows from strict monotonicity. -/
lemma idx_range_from_endpoints (m s : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (a b p : ℕ) (hab : a ≤ b) (hb : b ≤ s)
    (ha_le : equiEndpoint m s a ≤ p)
    (hp_lt : p < equiEndpoint m s b)
    (j : ℕ) (hj : j < s)
    (hj_lo : equiEndpoint m s j ≤ p)
    (hj_hi : p < equiEndpoint m s (j + 1)) :
    a ≤ j ∧ j < b := by
  constructor
  · -- a ≤ j: if j < a then equiEndpoint(j+1) ≤ equiEndpoint(a) ≤ p,
    -- contradicting p < equiEndpoint(j+1).
    by_contra h; push_neg at h
    have : equiEndpoint m s (j + 1) ≤ equiEndpoint m s a :=
      equiEndpoint_monotone (by omega)
    omega
  · -- j < b: if j ≥ b then equiEndpoint(b) ≤ equiEndpoint(j) ≤ p,
    -- contradicting p < equiEndpoint(b).
    by_contra h; push_neg at h
    have : equiEndpoint m s b ≤ equiEndpoint m s j :=
      equiEndpoint_monotone (by omega)
    omega

open Finpartition in
/-- The gap bound. -/
lemma gap_bound (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (q + 1) else r + (p - bd) / q
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2 := by
  simp only
  set q := m / s
  set r := m % s
  set bd := r * (q + 1)
  set idx := fun p => if p < bd then p / (q + 1) else r + (p - bd) / q
  set j₀ := idx v
  set jg := idx ((v + g) % m)
  -- Get interval bounds for v — convert to use j₀
  obtain ⟨hj₀_lt', hv_lo', hv_hi'⟩ :=
    idx_in_interval s m hs hs_le v hv_lt
  have hj₀_lt : j₀ < s := hj₀_lt'
  have hv_lo : equiEndpoint m s j₀ ≤ v := hv_lo'
  have hv_hi : v < equiEndpoint m s (j₀ + 1) := hv_hi'
  -- Get interval bounds for (v+g)%m — convert to use jg
  have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
  obtain ⟨hjg_lt', hvg_lo', hvg_hi'⟩ :=
    idx_in_interval s m hs hs_le ((v + g) % m) hvg_lt
  have hjg_lt : jg < s := hjg_lt'
  have hvg_lo : equiEndpoint m s jg ≤ (v + g) % m := hvg_lo'
  have hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1) := hvg_hi'
  -- Key bounds on v+g (before mod)
  have hpast : equiEndpoint m s (j₀ + 1) ≤ v + g :=
    shift_past_interval m s g hs h_lb j₀ v hv_lo hv_hi
  have hwithin : v + g < equiEndpoint m s (j₀ + 3) :=
    shift_within_two m s g h_ub j₀ v hv_hi
  have hg_lt_m : g < m := by
    have hqs : q * s ≤ m := Nat.div_mul_le_self m s
    have : 2 * q ≤ q * s := by nlinarith
    omega
  -- Helper: gap of 1 or 2 mod s gives the result
  have mod_small : ∀ d : ℕ, d = 1 ∨ d = 2 →
      d % s = 1 ∨ d % s = 2 := by
    intro d hd; rcases hd with h | h <;> [left; right] <;>
      rw [h] <;> exact Nat.mod_eq_of_lt (by omega)
  have mod_shift : ∀ d : ℕ, d = 1 ∨ d = 2 →
      (s + d) % s = 1 ∨ (s + d) % s = 2 := by
    intro d hd; rcases hd with h | h <;> subst h
    · left; show (s + 1) % s = 1
      rw [show s + 1 = 1 + s from by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    · right; show (s + 2) % s = 2
      rw [show s + 2 = 2 + s from by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  -- Case split on wrapping
  by_cases hvg_wrap : v + g < m
  · -- No wrapping: (v+g)%m = v+g
    have hvg_eq : (v + g) % m = v + g := Nat.mod_eq_of_lt hvg_wrap
    rw [hvg_eq] at hvg_lo hvg_hi
    by_cases hj3 : j₀ + 3 ≤ s
    · have hrange := idx_range_from_endpoints m s hs hs_le
        (j₀+1) (j₀+3) (v+g) (by omega) hj3 hpast hwithin
        jg hjg_lt hvg_lo hvg_hi
      -- jg - j₀ ∈ {1, 2}, so jg + s - j₀ = s + (jg - j₀)
      have : jg - j₀ = 1 ∨ jg - j₀ = 2 := by omega
      have : jg + s - j₀ = s + (jg - j₀) := by omega
      rw [this]; exact mod_shift _ ‹jg - j₀ = 1 ∨ _›
    · have hm_eq_ep : equiEndpoint m s s = m :=
        equiEndpoint_hi (by omega : s ≠ 0)
      have hvg_lt_ep : v + g < equiEndpoint m s s := by linarith
      have hrange := idx_range_from_endpoints m s hs hs_le
        (j₀+1) s (v+g) (by omega) (le_refl s) hpast hvg_lt_ep
        jg hjg_lt hvg_lo hvg_hi
      have : jg - j₀ = 1 ∨ jg - j₀ = 2 := by omega
      have : jg + s - j₀ = s + (jg - j₀) := by omega
      rw [this]; exact mod_shift _ ‹jg - j₀ = 1 ∨ _›
  · -- Wrapping: (v+g)%m = v+g-m
    push_neg at hvg_wrap
    have hvg_eq : (v + g) % m = v + g - m := by
      conv_lhs =>
        rw [show v + g = (v + g - m) + m from by omega]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hvg_eq] at hvg_lo hvg_hi
    -- j₀ ≥ s-2: if j₀ ≤ s-3, equiEndpoint(j₀+3) ≤ m,
    -- contradicting v+g ≥ m and v+g < equiEndpoint(j₀+3)
    have hj0_ge : j₀ ≥ s - 2 := by
      by_contra h; push_neg at h
      have : equiEndpoint m s (j₀ + 3) ≤ equiEndpoint m s s :=
        equiEndpoint_monotone (by omega)
      have := equiEndpoint_hi (by omega : s ≠ 0) (n := m) (k := s)
      omega
    have hr_lt : r < s := Nat.mod_lt m hs
    -- equiEndpoint(j₀+3) = q*(j₀+3) + r (since j₀+3 > s ≥ r)
    have hep_j3 : equiEndpoint m s (j₀ + 3) =
        q * (j₀ + 3) + r := by
      unfold equiEndpoint
      rw [min_eq_left (by omega : r ≤ j₀ + 3)]
    have hm_eq : m = q * s + r := by
      have h := Nat.div_add_mod m s
      rw [mul_comm] at h; exact h.symm
    -- m ≤ equiEndpoint(j₀+3)
    have hm_le_ep : m ≤ equiEndpoint m s (j₀ + 3) := by
      rw [hep_j3, hm_eq]
      have : q * s ≤ q * (j₀ + 3) :=
        Nat.mul_le_mul_left q (by omega)
      omega
    -- v+g-m < equiEndpoint(j₀+3-s) since
    -- equiEndpoint(j₀+3) - m = q*(j₀+3-s) ≤ equiEndpoint(j₀+3-s)
    have hep_diff : equiEndpoint m s (j₀ + 3) - m =
        q * (j₀ + 3 - s) := by
      rw [hep_j3, hm_eq]
      have : q * (j₀ + 3 - s) + q * s = q * (j₀ + 3) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
      omega
    have hvgm_ub : v + g - m <
        equiEndpoint m s (j₀ + 3 - s) := by
      have hvgm_lt : v + g - m < q * (j₀ + 3 - s) := by
        rw [← hep_diff]; omega
      have : q * (j₀ + 3 - s) ≤
          equiEndpoint m s (j₀ + 3 - s) := by
        change q * (j₀ + 3 - s) ≤
          q * (j₀ + 3 - s) + min r (j₀ + 3 - s)
        omega
      omega
    -- jg < j₀+3-s by idx_range_from_endpoints
    have hep0 : equiEndpoint m s 0 = 0 := by
      unfold equiEndpoint; simp
    have hrange := idx_range_from_endpoints m s hs hs_le
      0 (j₀ + 3 - s) (v + g - m) (by omega) (by omega)
      (by linarith) hvgm_ub jg hjg_lt hvg_lo hvg_hi
    -- j₀ ∈ {s-2, s-1} and jg < j₀+3-s, derive gap
    have : jg + s - j₀ = 1 ∨ jg + s - j₀ = 2 := by omega
    exact mod_small _ this
