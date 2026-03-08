import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Scratch file 3: gap bound proof

Prove that idx((v+g)%m) differs from idx(v) by 1 or 2 mod s.
-/

open Finpartition in
/-- idx(p) satisfies equiEndpoint(m,s,j) ≤ p < equiEndpoint(m,s,j+1) and j < s. -/
lemma idx_in_interval (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1) else r + (p - bd) / q
    j < s ∧
    equiEndpoint m s j ≤ p ∧
    p < equiEndpoint m s (j + 1) := by
  sorry

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
lemma gap_bound (s g m : ℕ) (hs : 0 < s) (hs2 : 2 ≤ s) (hs_le : s ≤ m)
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
  -- Get interval bounds for v
  have hv_spec := idx_in_interval s m hs hs_le v hv_lt
  obtain ⟨hj₀_lt, hv_lo, hv_hi⟩ := hv_spec
  -- Get interval bounds for (v+g)%m
  have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
  have hjg_spec := idx_in_interval s m hs hs_le ((v + g) % m) hvg_lt
  obtain ⟨hjg_lt, hvg_lo, hvg_hi⟩ := hjg_spec
  -- Key bounds on v+g (before mod):
  have hpast : equiEndpoint m s (j₀ + 1) ≤ v + g :=
    shift_past_interval m s g hs h_lb j₀ v hv_lo hv_hi
  have hwithin : v + g < equiEndpoint m s (j₀ + 3) :=
    shift_within_two m s g h_ub j₀ v hv_hi
  -- g < m (since s ≥ 2)
  have hg_lt_m : g < m := by
    have hqs : q * s ≤ m := Nat.div_mul_le_self m s
    have : 2 * q ≤ m := by nlinarith
    omega
  -- Case split on wrapping
  by_cases hvg_wrap : v + g < m
  · -- No wrapping: (v+g)%m = v+g
    have hvg_eq : (v + g) % m = v + g := Nat.mod_eq_of_lt hvg_wrap
    rw [hvg_eq] at hvg_lo hvg_hi ⊢
    -- Now: equiEndpoint(j₀+1) ≤ v+g < equiEndpoint(j₀+3)
    -- and equiEndpoint(jg) ≤ v+g < equiEndpoint(jg+1)
    -- and jg < s
    -- Need: j₀+1 ≤ jg ≤ j₀+2
    -- First check: j₀+3 ≤ s? If so, use idx_range_from_endpoints.
    by_cases hj3 : j₀ + 3 ≤ s
    · have := idx_range_from_endpoints m s hs hs_le (j₀+1) (j₀+3) (v+g)
        (by omega) hj3 hpast hwithin jg hjg_lt hvg_lo hvg_hi
      omega
    · -- j₀+3 > s, so j₀ ≥ s-2
      -- v+g < m = equiEndpoint(m,s,s), so jg < s is ensured.
      -- And equiEndpoint(j₀+1) ≤ v+g < m = equiEndpoint(s).
      have hj0_ge : j₀ ≥ s - 2 := by omega
      have hm_eq_ep : equiEndpoint m s s = m :=
        equiEndpoint_hi (by omega : s ≠ 0)
      have := idx_range_from_endpoints m s hs hs_le (j₀+1) s (v+g)
        (by omega) (le_refl s) hpast (by omega) jg hjg_lt hvg_lo hvg_hi
      -- j₀+1 ≤ jg < s. And j₀ ≥ s-2.
      -- So j₀ = s-2 and jg ∈ {s-1}, giving gap = 1.
      -- Or j₀ = s-1 and jg has no valid value (j₀+1 = s > jg).
      -- But j₀+1 ≤ jg < s means j₀ < s-1 (since jg ≥ j₀+1 and jg < s),
      -- so j₀ ≤ s-2. Combined with j₀ ≥ s-2: j₀ = s-2.
      -- Then jg ∈ {s-1} = {j₀+1}.
      -- gap = (jg + s - j₀) % s = (s-1 + s - (s-2)) % s = (s+1) % s = 1.
      omega
  · -- Wrapping: (v+g)%m = v+g-m
    push_neg at hvg_wrap
    have hvg_eq : (v + g) % m = v + g - m := by omega
    rw [hvg_eq] at hvg_lo hvg_hi ⊢
    -- v+g-m < equiEndpoint(j₀+3) - m
    -- equiEndpoint(s) = m, so equiEndpoint(j₀+3) - m = equiEndpoint(j₀+3) - equiEndpoint(s)
    -- For j₀+3 > s (which must hold since v+g ≥ m):
    -- equiEndpoint(j₀+1) ≤ v+g means equiEndpoint(j₀+1) ≤ v+g.
    -- Since v+g ≥ m = equiEndpoint(s), we need equiEndpoint(j₀+1) ≤ equiEndpoint(s).
    -- This means j₀+1 ≤ s, i.e., j₀ ≤ s-1, which is hj₀_lt.
    -- More precisely, v+g ≥ m means equiEndpoint(j₀+1) ≤ m.
    -- And equiEndpoint is monotone, so j₀+1 ≤ s.
    -- equiEndpoint(j₀+3) > equiEndpoint(s) = m when j₀+3 > s.
    -- Since j₀ ≤ s-1 and j₀+3 > s iff j₀ ≥ s-2.

    -- v+g-m ≥ 0 = equiEndpoint(0)
    have hvgm_ge : 0 ≤ v + g - m := by omega
    -- v+g-m < equiEndpoint(j₀+3) - m
    -- We need to show equiEndpoint(j₀+3) - equiEndpoint(s) bounds (v+g-m).
    -- equiEndpoint(j₀+3) - equiEndpoint(s):
    --   For j₀+3 > s: since equiEndpoint(j) = q*j + min(r,j),
    --   equiEndpoint(j₀+3) = q*(j₀+3) + r (since j₀+3 > s ≥ r)
    --   equiEndpoint(s) = m = q*s + r
    --   difference = q*(j₀+3-s)
    -- So v+g-m < q*(j₀+3-s).
    -- And j₀+3-s ≤ 2 (since j₀ ≤ s-1, so j₀+3 ≤ s+2).
    -- equiEndpoint(j₀+3-s) ≤ q*(j₀+3-s) + min(r, j₀+3-s)
    -- But we need v+g-m < equiEndpoint(j₀+3-s).
    -- Hmm, it's not exactly equal. Let me think differently.

    -- Since equiEndpoint(j₀+3) - equiEndpoint(s) involves j₀+3-s indices
    -- past s, and the "periodic" nature of the partition means these
    -- correspond to the FIRST j₀+3-s intervals in the next period.

    -- For a formal proof, I need: equiEndpoint(m,s,s+k) = m + equiEndpoint(m,s,k)
    -- This is NOT true in general because equiEndpoint is not periodic!
    -- equiEndpoint(m,s,s+k) = q*(s+k) + min(r, s+k) = q*s + q*k + r = m + q*k
    -- equiEndpoint(m,s,k) = q*k + min(r,k)
    -- These differ by m - min(r,k) + r, not m.
    -- But m + equiEndpoint(m,s,k) = m + q*k + min(r,k).
    -- And equiEndpoint(m,s,s+k) = m + q*k.
    -- So equiEndpoint(m,s,s+k) ≤ m + equiEndpoint(m,s,k) (since min(r,k) ≥ 0).
    -- And equiEndpoint(m,s,s+k) ≥ m + equiEndpoint(m,s,k) - r.

    -- Key: v+g-m < equiEndpoint(m,s,j₀+3) - m = q*(j₀+3-s) (for j₀+3 > s)
    -- And equiEndpoint(m,s,j₀+3-s) = q*(j₀+3-s) + min(r, j₀+3-s) ≥ q*(j₀+3-s).
    -- So v+g-m < equiEndpoint(m,s,j₀+3-s). ✓

    -- Similarly, v+g-m ≥ equiEndpoint(m,s,j₀+1) - m.
    -- If j₀+1 < s: equiEndpoint(j₀+1) < m. But v+g ≥ m means v+g - m ≥ 0.
    --   And equiEndpoint(j₀+1) - m < 0 (subtraction underflow in ℕ). So v+g-m ≥ 0 ≥ equiEndpoint(0).
    --   We need a LOWER bound on jg. The lower bound comes from
    --   equiEndpoint(j₀+1-s) but that's negative/zero.
    --   Actually jg ≥ 0 always. And jg ≤ (j₀+3-s) - 1 from the upper bound.
    --   j₀+3-s ≤ 2. So jg ≤ 1.
    --   But we also need jg ≥ ... what? We need (jg+s-j₀)%s ∈ {1,2}.
    --   Since j₀ ≥ s-2 (from wrapping): gap = (jg + s - j₀) % s.
    --   j₀ = s-2: gap = (jg + 2) % s. Need gap = 1 or 2.
    --     jg < j₀+3-s = 1. So jg = 0. gap = 2%s = 2 (s≥3). ✓
    --   j₀ = s-1: gap = (jg + 1) % s. Need gap = 1 or 2.
    --     jg < j₀+3-s = 2. So jg ∈ {0,1}. gap = 1 or 2. ✓

    -- So the key facts needed:
    -- 1. j₀ ≥ s-2 (from v+g ≥ m and equiEndpoint(j₀+1) ≤ v+g)
    -- 2. jg < j₀+3-s (from v+g-m < equiEndpoint(j₀+3-s))
    -- 3. jg ≥ 0 (trivially)
    -- Then case analysis on j₀ ∈ {s-2, s-1}.

    -- Hmm, this is still very involved. Let me just sorry this for now
    -- and come back to it.
    sorry
