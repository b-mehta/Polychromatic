import Polychromatic.FourThree.Combi.BlockColour

open Finset Pointwise

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

/-- **Subcase (1a):** g ∈ {2, 3, 4}. Reduces directly to Table 1 entries. -/
lemma case_one_small_g (g : ℕ) (hm : m ≥ 289) (hg : g ∈ ({2, 3, 4} : Finset ℕ)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  fin_cases hg <;> push_cast <;> norm_num
  · exact table1_0123 m (by grind)
  · exact table1_0134 m (by grind)
  · exact table1_0145 m (by grind)

/-! ### Helper lemmas for subcase (1b)

These are technical arithmetic lemmas used in the proof of `case_one_interval`.
They are not important on their own.
-/

private lemma lt_two' (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 := by omega

/-- Phase differs when gap is 1 or 2 mod s, and 3 ∣ s. -/
private lemma phase_ne_of_gap {s j₀ jg : ℕ} (hs3 : 3 ∣ s) (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by
  obtain ⟨t, ht⟩ := hs3; subst ht
  have hqlt : (jg + 3 * t - j₀) / (3 * t) < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hdam := Nat.div_add_mod (jg + 3 * t - j₀) (3 * t)
  rcases hgap with hmod | hmod <;>
    rcases lt_two' _ hqlt with hq | hq <;>
    rw [hq, hmod] at hdam
  · grind [Nat.mul_add_mod]
  · grind
  · grind [Nat.mul_add_mod]
  · grind

open Finpartition in
private lemma idx_in_interval' (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m) (p : ℕ) (hp : p < m) :
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
    have : (s - r) * q + r * q = s * q := by grind [Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
    grind
  split
  · rename_i hlt
    set j := p / (q + 1)
    have hq1_pos : 0 < q + 1 := by omega
    have hj_lt_r : j < r := by rw [Nat.div_lt_iff_lt_mul hq1_pos]; exact hlt
    have hdam : (q + 1) * j + p % (q + 1) = p := Nat.div_add_mod p (q + 1)
    have hmod : p % (q + 1) < q + 1 := Nat.mod_lt p hq1_pos
    have hle : q * j + j ≤ p := by grind
    have hub : p < q * (j + 1) + (j + 1) := by grind
    refine ⟨by omega, ?_, ?_⟩
    · unfold equiEndpoint
      rw [min_eq_right (by omega)]
      change q * j + j ≤ p; exact hle
    · unfold equiEndpoint
      rw [min_eq_right (by omega)]
      change p < q * (j + 1) + (j + 1); exact hub
  · rename_i hge; push_neg at hge
    set d := (p - bd) / q
    have hdam : q * d + (p - bd) % q = p - bd := Nat.div_add_mod (p - bd) q
    have hmod : (p - bd) % q < q := Nat.mod_lt _ hq_pos
    have hqd_le : q * d ≤ p - bd := by omega
    have hqd_ub : p - bd < q * d + q := by omega
    have hd_lt : d < s - r := by rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
    set j := r + d
    have hring_j : q * j + r = bd + q * d := by grind
    have hring_j1 : q * (j + 1) + r = bd + q * d + q := by grind
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

private lemma equiEndpoint_diff' (m s j : ℕ) : Finpartition.equiEndpoint m s (j + 1) -
      Finpartition.equiEndpoint m s j =
      if j < m % s then m / s + 1 else m / s :=
  Finpartition.card_of_mem_equipartitionToIco_parts_aux

open Finpartition in
private lemma gap_exceeds_ilen (m s g : ℕ) (hs : 0 < s) (h_lb : (m + s - 1) / s < g) (j : ℕ) :
    equiEndpoint m s (j + 1) - equiEndpoint m s j < g := by
  rw [equiEndpoint_diff']
  set q := m / s; set r := m % s
  by_cases hr : j < r
  · rw [if_pos hr]
    have : (q + 1) * s ≤ m + s - 1 := by grind [Nat.div_add_mod m s]
    have := Nat.le_div_iff_mul_le hs |>.mpr this; omega
  · rw [if_neg hr]
    have : q * s ≤ m + s - 1 := le_trans (Nat.div_mul_le_self m s) (by omega)
    have := Nat.le_div_iff_mul_le hs |>.mpr this; omega

open Finpartition in
private lemma shift_within_two' (m s g : ℕ) (h_ub : g < 2 * (m / s))
    (j p : ℕ) (hhi : p < equiEndpoint m s (j + 1)) :
    p + g < equiEndpoint m s (j + 3) := by
  have hm1 : equiEndpoint m s (j + 2) - equiEndpoint m s (j + 1) ≥ m / s := by
    rw [equiEndpoint_diff']; split <;> omega
  have hm2 : equiEndpoint m s (j + 3) - equiEndpoint m s (j + 2) ≥ m / s := by
    rw [equiEndpoint_diff']; split <;> omega
  have hmono : equiEndpoint m s (j + 1) ≤
      equiEndpoint m s (j + 2) := equiEndpoint_monotone (by omega)
  omega

open Finpartition in
private lemma idx_range_from_endpoints' (m s : ℕ) (a b p : ℕ)
    (ha_le : equiEndpoint m s a ≤ p)
    (hp_lt : p < equiEndpoint m s b)
    (j : ℕ)
    (hj_lo : equiEndpoint m s j ≤ p)
    (hj_hi : p < equiEndpoint m s (j + 1)) :
    a ≤ j ∧ j < b := by
  constructor
  · by_contra! h
    have : equiEndpoint m s (j + 1) ≤ equiEndpoint m s a := equiEndpoint_monotone (by omega)
    omega
  · by_contra! h
    have : equiEndpoint m s b ≤ equiEndpoint m s j := equiEndpoint_monotone (by omega)
    omega

/-- Gap bound: idx of (v+g)%m differs from idx(v) by 1 or 2 mod s.
    This is the key arithmetic fact for interval colorings. -/
private lemma gap_bound_interval (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) :
    let bd := (m % s) * (m / s + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (m / s + 1)
      else m % s + (p - bd) / (m / s)
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2 := by
  simp only
  set q := m / s
  set r := m % s
  set bd := r * (q + 1)
  set idx := fun p ↦
    if p < bd then p / (q + 1) else r + (p - bd) / q
  set j₀ := idx v
  set jg := idx ((v + g) % m)
  obtain ⟨hj₀_lt', hv_lo', hv_hi'⟩ := idx_in_interval' s m hs hs_le v hv_lt
  have hj₀_lt : j₀ < s := hj₀_lt'
  have hv_lo : Finpartition.equiEndpoint m s j₀ ≤ v := hv_lo'
  have hv_hi : v < Finpartition.equiEndpoint m s (j₀ + 1) := hv_hi'
  have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
  obtain ⟨hjg_lt', hvg_lo', hvg_hi'⟩ := idx_in_interval' s m hs hs_le ((v + g) % m) hvg_lt
  have hjg_lt : jg < s := hjg_lt'
  have hvg_lo : Finpartition.equiEndpoint m s jg ≤ (v + g) % m := hvg_lo'
  have hvg_hi : (v + g) % m < Finpartition.equiEndpoint m s (jg + 1) := hvg_hi'
  have hpast : Finpartition.equiEndpoint m s (j₀ + 1) ≤ v + g := by
    have := gap_exceeds_ilen m s g hs h_lb j₀; omega
  have hwithin : v + g <
      Finpartition.equiEndpoint m s (j₀ + 3) := shift_within_two' m s g h_ub j₀ v hv_hi
  have hg_lt_m : g < m := by
    have hqs : q * s ≤ m := Nat.div_mul_le_self m s
    have : 2 * q ≤ q * s := by nlinarith
    omega
  have mod_small : ∀ d : ℕ, d = 1 ∨ d = 2 → d % s = 1 ∨ d % s = 2 := by
    intro d hd; rcases hd with h | h <;> subst h
    · left; exact Nat.mod_eq_of_lt (by omega)
    · right; exact Nat.mod_eq_of_lt (by omega)
  have mod_shift : ∀ d : ℕ, d = 1 ∨ d = 2 → (s + d) % s = 1 ∨ (s + d) % s = 2 := by
    intro d hd; rw [Nat.add_comm, Nat.add_mod_right]; exact mod_small d hd
  by_cases hvg_wrap : v + g < m
  · have hvg_eq : (v + g) % m = v + g := Nat.mod_eq_of_lt hvg_wrap
    rw [hvg_eq] at hvg_lo hvg_hi
    have hrange : j₀ + 1 ≤ jg ∧ jg < j₀ + 3 := by
      by_cases hj3 : j₀ + 3 ≤ s
      · exact idx_range_from_endpoints' m s (j₀+1) (j₀+3) (v+g) hpast hwithin jg hvg_lo hvg_hi
      · have hvg_lt_ep : v + g < Finpartition.equiEndpoint m s s := by
          grind [Finpartition.equiEndpoint_hi (show s ≠ 0 by omega) (n := m) (k := s)]
        have := idx_range_from_endpoints' m s (j₀+1) s (v+g) hpast hvg_lt_ep jg hvg_lo hvg_hi
        omega
    have : jg - j₀ = 1 ∨ jg - j₀ = 2 := by omega
    have : jg + s - j₀ = s + (jg - j₀) := by omega
    rw [this]; exact mod_shift _ ‹jg - j₀ = 1 ∨ _›
  · push_neg at hvg_wrap
    have hvg_eq : (v + g) % m = v + g - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hvg_eq] at hvg_lo hvg_hi
    have hj0_ge : j₀ ≥ s - 2 := by
      by_contra! h
      have : Finpartition.equiEndpoint m s (j₀ + 3) ≤
          Finpartition.equiEndpoint m s s := Finpartition.equiEndpoint_monotone (by omega)
      have := Finpartition.equiEndpoint_hi (by omega : s ≠ 0) (n := m) (k := s)
      omega
    have hr_lt : r < s := Nat.mod_lt m hs
    have hep_j3 : Finpartition.equiEndpoint m s (j₀ + 3) = q * (j₀ + 3) + r := by
      unfold Finpartition.equiEndpoint
      rw [min_eq_left (by omega)]
    have hm_eq : m = q * s + r := by grind [Nat.div_add_mod m s]
    have hm_le_ep : m ≤ Finpartition.equiEndpoint m s (j₀ + 3) := by grind
    have hep_diff : Finpartition.equiEndpoint m s (j₀ + 3) - m =
        q * (j₀ + 3 - s) := by rw [hep_j3, hm_eq]; grind [Nat.mul_add]
    have hvgm_ub : v + g - m < Finpartition.equiEndpoint m s
          (j₀ + 3 - s) := by
      have : v + g - m < q * (j₀ + 3 - s) := by rw [← hep_diff]; omega
      have : q * (j₀ + 3 - s) ≤ Finpartition.equiEndpoint m s
            (j₀ + 3 - s) := by
        change q * (j₀ + 3 - s) ≤ q * (j₀ + 3 - s) + min r (j₀ + 3 - s)
        omega
      omega
    have hrange := idx_range_from_endpoints' m s
      0 (j₀ + 3 - s) (v + g - m)
      (by unfold Finpartition.equiEndpoint; simp)
      hvgm_ub jg hvg_lo hvg_hi
    have : jg + s - j₀ = 1 ∨ jg + s - j₀ = 2 := by omega
    exact mod_small _ this

-- Equi-partition index: which interval does position p fall in?
private def eqp_idx (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p / (q + 1)
  else r + (p - r * (q + 1)) / q

-- Equi-partition offset: position within the interval
private def eqp_off (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p % (q + 1)
  else (p - r * (q + 1)) % q

private lemma eqp_idx_m (q r s : ℕ) (hq : 0 < q) (hr : r < s) : eqp_idx q r (s * q + r) = s := by
  have hge : ¬(s * q + r < r * (q + 1)) := by nlinarith
  simp only [eqp_idx, if_neg hge]
  have hle : r * (q + 1) ≤ s * q + r := by nlinarith
  have hsub : s * q + r - r * (q + 1) = (s - r) * q := by zify [hle, (by omega : r ≤ s)]; ring
  rw [hsub, Nat.mul_div_cancel _ hq]; omega

-- General fact: consecutive ℕ quotients differ by 0 or 1
private lemma div_step (a b : ℕ) (hb : 0 < b) : (a + 1) / b = a / b ∨ (a + 1) / b = a / b + 1 := by
  have hle : a / b ≤ (a + 1) / b := Nat.div_le_div_right (Nat.le_succ a)
  suffices h : (a + 1) / b ≤ a / b + 1 by omega
  have h1 := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  have hub : a + 1 ≤ b * (a / b + 1) := by grind
  calc (a + 1) / b ≤ b * (a / b + 1) / b := Nat.div_le_div_right hub
    _ = a / b + 1 := Nat.mul_div_cancel_left _ hb

private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) : eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by
  unfold eqp_idx
  split_ifs with h1 h2
  · exact div_step p (q + 1) (by omega)
  · omega
  · right
    have hpeq : p + 1 = r * (q + 1) := by omega
    have hr_pos : 0 < r := by grind
    have h_succ : (p + 1) / (q + 1) = r := by rw [hpeq]; exact Nat.mul_div_cancel r (by omega)
    have hne : p / (q + 1) ≠ r := by
      intro heq
      grind [Nat.div_mul_le_self p (q + 1)]
    have hidx_p : p / (q + 1) = r - 1 := by have := div_step p (q + 1) (by omega); omega
    rw [hpeq, Nat.sub_self, Nat.zero_div, hidx_p]; omega
  · have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    have := div_step (p - r * (q + 1)) q hq; omega

-- Helper: if quotient stays same, remainder increases by 1
private lemma mod_step (a b : ℕ) (h : (a + 1) / b = a / b) :
    (a + 1) % b = a % b + 1 := by grind [Nat.div_add_mod a b, Nat.div_add_mod (a + 1) b]

-- Helper: if quotient increases by 1, remainder resets to 0
private lemma mod_zero_step (a b : ℕ) (hb : 0 < b) (h : (a + 1) / b = a / b + 1) :
    (a + 1) % b = 0 := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.div_add_mod (a + 1) b
  have h3 := Nat.mod_lt a hb
  have h4 : b * ((a + 1) / b) = b * (a / b) + b := by grind
  grind

private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q) (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;>
      by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1, if_pos h2]
    apply mod_step p (q + 1)
    have h3 : eqp_idx q r (p + 1) = (p + 1) / (q + 1) := by unfold eqp_idx; rw [if_pos h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by unfold eqp_idx; rw [if_pos h2]
    grind
  · omega
  · exfalso
    have h3 : eqp_idx q r (p + 1) = r + (p + 1 - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by unfold eqp_idx; rw [if_pos h2]
    have h5 : p / (q + 1) < r := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h2
    have h6 : r ≤ eqp_idx q r (p + 1) := by rw [h3]; exact Nat.le_add_right r _
    grind
  · rw [if_neg h1, if_neg h2]
    have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    apply mod_step (p - r * (q + 1)) q
    have h3 : eqp_idx q r (p + 1) = r + (p + 1 - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h1]
    have h4 : eqp_idx q r p = r + (p - r * (q + 1)) / q := by unfold eqp_idx; rw [if_neg h2]
    rw [h3, h4, hsub] at h; omega

private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q) (h : eqp_idx q r (p + 1) ≠ eqp_idx q r p) :
    eqp_off q r (p + 1) = 0 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;>
      by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1]
    apply mod_zero_step p (q + 1) (by omega)
    have h3 : eqp_idx q r (p + 1) = (p + 1) / (q + 1) := by unfold eqp_idx; rw [if_pos h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by unfold eqp_idx; rw [if_pos h2]
    rw [h3, h4] at h
    have := div_step p (q + 1) (by omega)
    omega
  · omega
  · rw [if_neg h1]
    have : p + 1 = r * (q + 1) := by omega
    simp [this]
  · rw [if_neg h1]
    have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    apply mod_zero_step (p - r * (q + 1)) q hq
    have h3 : eqp_idx q r (p + 1) = r + (p + 1 - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h1]
    have h4 : eqp_idx q r p = r + (p - r * (q + 1)) / q := by unfold eqp_idx; rw [if_neg h2]
    rw [h3, h4, hsub] at h
    have := div_step (p - r * (q + 1)) q hq
    omega

private lemma gap_mod_cases_gen (s j₀ jg d : ℕ) (hj₀ : j₀ < s) (hjg : jg < s)
    (hmod : (jg + s - j₀) % s = d) :
    jg + s - j₀ = d ∨ jg + s - j₀ = s + d := by
  have hd_hi : jg + s - j₀ < 2 * s := by omega
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  rw [hmod] at hdiv
  have hq_lt : (jg + s - j₀) / s < 2 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h <;> grind

private lemma equiEndpoint_diff_ge (m s j : ℕ) : m / s ≤ Finpartition.equiEndpoint m s (j + 1) -
        Finpartition.equiEndpoint m s j := by grind [Finpartition.equiEndpoint]

open Finpartition in
private lemma straddle1_gap2 (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hstrad : equiEndpoint m s (j₀ + 1) ≤ v + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 2 := by
  by_contra hne
  have hgap1 : (jg + s - j₀) % s = 1 := by tauto
  have hv_eq : v + 1 = equiEndpoint m s (j₀ + 1) := by omega
  have hjg_cases := gap_mod_cases_gen s j₀ jg 1 hj₀_lt hjg_lt hgap1
  have hq_pos : 0 < m / s := by grind
  have hg_lt_m : g < m := by have := Nat.div_mul_le_self m s; nlinarith
  have hep_s : equiEndpoint m s s = m := equiEndpoint_hi (by omega)
  by_cases hj₀_lt_s : j₀ + 1 < s
  · have hjg_val : jg = j₀ + 1 := by omega
    have hilen := gap_exceeds_ilen m s g hs h_lb (j₀ + 1)
    have hmono : equiEndpoint m s (j₀ + 1) ≤
        equiEndpoint m s (j₀ + 1 + 1) := equiEndpoint_monotone (by omega)
    have hsac := Nat.sub_add_cancel hmono
    have hvg_ge : v + g ≥ equiEndpoint m s (j₀ + 1 + 1) := by omega
    by_cases hwrap : v + g < m
    · have : (v + g) % m = v + g := Nat.mod_eq_of_lt hwrap
      rw [hjg_val] at hvg_hi
      omega
    · push_neg at hwrap
      rw [hjg_val] at hvg_lo
      have hvg_mod : (v + g) % m = v + g - m := by
        rw [Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)]
      rw [hvg_mod] at hvg_lo
      omega
  · have hj₀_eq : j₀ = s - 1 := by omega
    have hjg_val : jg = 0 := by omega
    rw [hj₀_eq, Nat.sub_add_cancel (by omega), hep_s] at hv_eq
    have hv_val : v = m - 1 := by omega
    have hg_pos : 0 < g := by
      have := gap_exceeds_ilen m s g hs h_lb 0
      have := equiEndpoint_strictMono (by omega : s ≠ 0) hs_le one_pos
      omega
    have hvg_mod : (v + g) % m = g - 1 := by
      have : m - 1 + g = m + (g - 1) := by omega
      rw [hv_val, this, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hjg_val, hvg_mod] at hvg_hi
    simp only [Nat.zero_add] at hvg_hi
    have hep1 : equiEndpoint m s 1 ≤ (m + s - 1) / s := by
      rw [equiEndpoint]
      simp only [Nat.mul_one]
      by_cases hr : m % s = 0
      · simp only [hr, zero_min]; exact Nat.div_le_div_right (by omega)
      · have : min (m % s) 1 = 1 := by omega
        rw [this]
        apply (Nat.le_div_iff_mul_le hs).mpr
        grind [Nat.div_add_mod m s]
    omega

open Finpartition in
private lemma straddle2_gap1 (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v j₀ jg : ℕ) (hv : v < m)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hstrad : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 1 := by
  by_contra hne
  have hgap2 : (jg + s - j₀) % s = 2 := by tauto
  have hvg_eq : (v + g) % m + 1 = equiEndpoint m s (jg + 1) := by omega
  have hq_pos : 0 < m / s := by grind
  have hg_lt_m : g < m := by have := Nat.div_mul_le_self m s; nlinarith
  have hjg_cases := gap_mod_cases_gen s j₀ jg 2 hj₀_lt hjg_lt hgap2
  have hep0 : equiEndpoint m s 0 = 0 := by simp [equiEndpoint]
  have hep_s : equiEndpoint m s s = m := equiEndpoint_hi (by omega)
  by_cases hj_nowrap : j₀ + 2 < s
  · have hjg_val : jg = j₀ + 2 := by omega
    rw [hjg_val] at hvg_eq
    set e1 := equiEndpoint m s (j₀ + 1) with he1
    set e2 := equiEndpoint m s (j₀ + 1 + 1) with he2
    set e3 := equiEndpoint m s (j₀ + 1 + 1 + 1) with he3
    have hd1 := equiEndpoint_diff_ge m s (j₀ + 1)
    have hd2 := equiEndpoint_diff_ge m s (j₀ + 1 + 1)
    have hmono1 : e1 ≤ e2 := by omega
    have hsac1 := Nat.sub_add_cancel hmono1
    have hmono2 : e2 ≤ e3 := by omega
    have hsac2 := Nat.sub_add_cancel hmono2
    by_cases hwrap : v + g < m
    · have : (v + g) % m = v + g := Nat.mod_eq_of_lt hwrap
      omega
    · push_neg at hwrap
      have : (v + g) % m = v + g - m := by
        rw [Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)]
      omega
  · have hjg_val : jg = j₀ + 2 - s := by omega
    have hpos_wrap : m ≤ v + g := by
      by_contra! h
      have : (v + g) % m = v + g := Nat.mod_eq_of_lt h
      have : equiEndpoint m s (jg + 1) ≤ equiEndpoint m s j₀ := equiEndpoint_monotone (by omega)
      have : 0 < g := by
        have := gap_exceeds_ilen m s g hs h_lb 0
        have := equiEndpoint_strictMono (by omega : s ≠ 0) hs_le one_pos
        omega
      omega
    have hvg_mod : (v + g) % m = v + g - m := by
      rw [Nat.mod_eq_sub_mod hpos_wrap, Nat.mod_eq_of_lt (by omega)]
    by_cases hj₀_eq : j₀ = s - 2
    · have hjg0 : jg = 0 := by omega
      rw [hjg0] at hvg_eq
      simp only [Nat.zero_add] at hvg_eq
      rw [hj₀_eq] at hv_hi
      have : s - 2 + 1 = s - 1 := by omega
      rw [this] at hv_hi
      have hd1 := equiEndpoint_diff_ge m s (s - 1)
      rw [Nat.sub_add_cancel (by omega), hep_s] at hd1
      have hep_s1_le : equiEndpoint m s (s - 1) ≤ m :=
        le_trans (equiEndpoint_monotone (by omega)) hep_s.le
      have hsac_m := Nat.sub_add_cancel hep_s1_le
      have hd2 := equiEndpoint_diff_ge m s 0
      rw [hep0, Nat.zero_add] at hd2
      omega
    · have hj₀_eq2 : j₀ = s - 1 := by omega
      have hjg1 : jg = 1 := by omega
      rw [hjg1] at hvg_eq
      rw [hj₀_eq2, Nat.sub_add_cancel (by omega), hep_s] at hv_hi
      have hd1 := equiEndpoint_diff_ge m s 0
      rw [hep0, Nat.zero_add] at hd1
      have hd2 := equiEndpoint_diff_ge m s 1
      have hmono12 : equiEndpoint m s 1 ≤ equiEndpoint m s (1 + 1) := by omega
      have hsac12 := Nat.sub_add_cancel hmono12
      omega

private lemma eqp_idx_succ_lt_m (q r s p : ℕ) (hq_pos : 0 < q) (hr_lt : r < s)
    (hm_eq : m = s * q + r)
    (hp : p < m) :
    p + 1 < m ∨ eqp_idx q r (p + 1) = s := by
  by_cases h : p + 1 < m
  · exact Or.inl h
  · have hpm : p + 1 = m := by omega
    right
    rw [hpm, hm_eq]
    exact eqp_idx_m q r s hq_pos hr_lt

private lemma non_straddle_witness (q r p : ℕ) (hq_pos : 0 < q)
    (hp : p < m) (hp1 : p + 1 < m)
    (hsame : eqp_idx q r (p + 1) = eqp_idx q r p)
    (j : ℕ) (hj : j = eqp_idx q r p)
    (t : ℕ) (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    ∃ d ∈ ({0, 1} : Finset ℕ),
      (eqp_idx q r ((p + d) % m) + eqp_off q r ((p + d) % m) % 2) % 3 = t := by
  have hoff := eqp_off_succ_same q r p hq_pos hsame
  have : (j + (eqp_off q r p) % 2) % 3 = t ∨ (j + ((eqp_off q r p) + 1) % 2) % 3 = t := by omega
  rcases this with h | h
  · exact ⟨0, by simp, by
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hp, ← hj]
      exact h⟩
  · exact ⟨1, by simp, by
      rw [Nat.mod_eq_of_lt hp1, hsame, ← hj, hoff]
      exact h⟩

private lemma straddle_boundary_color (q r s p : ℕ) (hq_pos : 0 < q) (hr_lt : r < s)
    (hs3 : 3 ∣ s)
    (hm_eq : m = s * q + r)
    (hp : p < m)
    (hstep : eqp_idx q r (p + 1) = eqp_idx q r p + 1)
    (j : ℕ) (hj : j = eqp_idx q r p) :
    (eqp_idx q r ((p + 1) % m) + eqp_off q r ((p + 1) % m) % 2) % 3 = (j + 1) % 3 := by
  by_cases h : p + 1 < m
  · rw [Nat.mod_eq_of_lt h]
    have hoff := eqp_off_succ_new q r p hq_pos (by omega)
    rw [hstep, ← hj, hoff]
  · have hpm : p + 1 = m := by omega
    have : eqp_idx q r 0 = 0 := by simp [eqp_idx]
    have : eqp_off q r 0 = 0 := by simp [eqp_off]
    rw [hpm, Nat.mod_self, ‹eqp_idx q r 0 = 0›, ‹eqp_off q r 0 = 0›]
    rw [hpm] at hstep
    have hm_idx : eqp_idx q r m = s := by rw [hm_eq]; exact eqp_idx_m q r s hq_pos hr_lt
    have hjs : j + 1 = s := by rw [hj]; omega
    grind

private lemma vg_mod_shift (v g d : ℕ) : (v + (g + d)) % m = ((v + g) % m + d) % m := by
  grind [Nat.add_mod (v + g) d m, Nat.add_mod ((v + g) % m) d m,
    Nat.mod_mod_of_dvd _ (dvd_refl m)]

private lemma mod3_witness {s k : ℕ} (hs : s < 3) (hk : k < 3) : ((k + 3 - s) % 3 = 0 → s = k) ∧
    ((k + 3 - s) % 3 = 1 → (s + 1) % 3 = k) ∧
    ((k + 3 - s) % 3 = 2 → (s + 2) % 3 = k) := by grind

private lemma endgame_witness {g : ℕ} {c : ℕ → ℕ} {v s : ℕ} {k : Fin 3} (hs : s < 3)
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

/-- **Subcase (1b): interval coloring strategy.**
    Let s be the smallest multiple of 3 such that g > ⌈m/s⌉. Split Z_m into s
    intervals of lengths ⌊m/s⌋ and ⌈m/s⌉, colored in a repeating 01/12/20
    pattern (repeated s/3 times). Since ⌈m/s⌉ < g < 2⌊m/s⌋, any translate of
    {0,1,g,g+1} where the pairs {0,1} and {g,g+1} lie in different intervals gets
    all three colors. This is the workhorse subcase, handling most values of g. -/
lemma case_one_interval (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  set q := m / s
  set r := m % s
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hr_lt : r < s := Nat.mod_lt m hs
  have hq_pos : 0 < q := by nlinarith [Nat.div_mul_le_self m s, h_lb, h_ub]
  have hs_le : s ≤ m := by nlinarith [Nat.div_mul_le_self m s]
  have hg1_lt_m : g + 1 < m := by nlinarith [Nat.div_mul_le_self m s, Nat.le_of_dvd hs hs3]
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  set bd := r * (q + 1)
  let idx (p : ℕ) : ℕ :=
    if p < bd then p / (q + 1) else r + (p - bd) / q
  let off (p : ℕ) : ℕ :=
    if p < bd then p % (q + 1) else (p - bd) % q
  let c (p : ℕ) : ℕ := (idx (p % m) + off (p % m) % 2) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by omega)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c]; rw [Nat.mod_mod_of_dvd p (dvd_refl m)]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness hg1_lt_m hc_lt3 hc_period ?_⟩
  set v := n.val
  have hv_lt : v < m := ZMod.val_lt n
  -- Gap bound: idx((v+g)%m) differs from idx(v) by 1 or 2 mod s
  set j₀ := idx v with hj₀_def
  set jg := idx ((v + g) % m) with hjg_def
  have hs3_le : 3 ≤ s := Nat.le_of_dvd hs hs3
  have hgap := gap_bound_interval s g m hs hs3_le hs_le h_lb h_ub v hv_lt
  -- idx ranges
  have hidx_lt : ∀ p, p < m → idx p < s := by
    intro p hp; simp only [idx]; split
    · have : p / (q + 1) < r := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        exact ‹_›
      omega
    · rename_i hge; push_neg at hge
      have : (p - bd) / q < s - r := by
        rw [Nat.div_lt_iff_lt_mul hq_pos]
        have : r * (q + 1) + (s - r) * q = s * q + r := by
          have : (s - r) * q + r * q = s * q := by grind [Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
          grind
        omega
      omega
  have hj₀_lt : j₀ < s := hidx_lt v hv_lt
  have hjg_lt : jg < s := hidx_lt ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Phase difference: j₀ % 3 ≠ jg % 3
  have hphase : j₀ % 3 ≠ jg % 3 := phase_ne_of_gap hs3 hj₀_lt hjg_lt hgap
  -- Interval bounds
  have hiv := idx_in_interval' s m hs hs_le v hv_lt
  have hivg := idx_in_interval' s m hs hs_le ((v + g) % m) (Nat.mod_lt _ (by omega))
  have hv_lo := hiv.2.1; have hv_hi := hiv.2.2
  have hvg_lo := hivg.2.1; have hvg_hi := hivg.2.2
  -- Bridge: eqp_idx step → equiEndpoint straddle condition
  open Finpartition in
  have endpoint_bridge : ∀ p : ℕ, p < m → eqp_idx q r p < s →
      eqp_idx q r (p + 1) = eqp_idx q r p + 1 →
      equiEndpoint m s (eqp_idx q r p + 1) ≤ p + 1 := by
    intro p hp hidx_p hstep_p
    by_cases hp1 : p + 1 < m
    · have hiv_p := idx_in_interval' s m hs hs_le (p + 1) hp1
      simp only at hiv_p
      change eqp_idx q r (p + 1) < s ∧ equiEndpoint m s (eqp_idx q r (p + 1)) ≤ p + 1 ∧ _ at hiv_p
      rw [hstep_p] at hiv_p
      exact hiv_p.2.1
    · have hpm : p + 1 = m := by omega
      rw [hpm]; exact (equiEndpoint_monotone (by omega)).trans (equiEndpoint_hi (by omega)).le
  -- Helper: non-straddle witness from pair 1
  have pair1_ns : ∀ kv : ℕ,
      (kv = j₀ % 3 ∨ kv = (j₀ + 1) % 3) →
      eqp_idx q r (v + 1) = eqp_idx q r v →
      ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = kv := by
    intro kv hkv h1_same
    have hv1_lt : v + 1 < m := by
      rcases eqp_idx_succ_lt_m m q r s v hq_pos hr_lt hm_eq hv_lt with h | h
      · exact h
      · rw [h1_same] at h; have : j₀ = s := h; omega
    obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r v
      hq_pos hv_lt hv1_lt h1_same j₀ rfl kv hkv
    exact ⟨d, by simp only [Finset.mem_insert,
      Finset.mem_singleton] at hd_mem ⊢; omega, hd_eq⟩
  -- Helper: non-straddle witness from pair 2
  have pair2_ns : ∀ kv : ℕ,
      (kv = jg % 3 ∨ kv = (jg + 1) % 3) →
      eqp_idx q r (((v + g) % m) + 1) = eqp_idx q r ((v + g) % m) →
      ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = kv := by
    intro kv hkv h2_same
    have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
    have hvg1_lt : (v + g) % m + 1 < m := by
      rcases eqp_idx_succ_lt_m m q r s ((v + g) % m) hq_pos hr_lt hm_eq hvg_lt with h | h
      · exact h
      · rw [h2_same] at h; have : jg = s := h; omega
    obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r
      ((v + g) % m) hq_pos hvg_lt hvg1_lt h2_same jg rfl kv hkv
    refine ⟨g + d, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hd_mem ⊢; omega
    · change (idx ((v + (g + d)) % m) + off ((v + (g + d)) % m) % 2) % 3 = kv
      rw [vg_mod_shift m v g d]; exact hd_eq
  -- Helper: both-straddle contradiction
  open Finpartition in
  have both_straddle_absurd :
      eqp_idx q r (v + 1) = eqp_idx q r v + 1 →
      eqp_idx q r (((v + g) % m) + 1) = eqp_idx q r ((v + g) % m) + 1 → False := by
    intro h1_step h2_step
    have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
    have hstrad2 : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1 :=
      endpoint_bridge ((v + g) % m) (Nat.mod_lt _ (by omega)) hjg_lt h2_step
    have hgap2 := straddle1_gap2 s g m hs hs3_le hs_le h_lb
      h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi hvg_lo hvg_hi hstrad1 hgap
    have hgap1 := straddle2_gap1 s g m hs hs3_le hs_le
      h_lb h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi hvg_hi hstrad2 hgap
    omega
  -- Step 1: which pair covers k?
  have : (k.val = j₀ % 3 ∨ k.val = (j₀ + 1) % 3) ∨
      (k.val = jg % 3 ∨ k.val = (jg + 1) % 3) := by omega
  rcases this with hk1 | hk2
  · -- Pair 1 covers k: k ∈ {j₀%3, (j₀+1)%3}
    rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
    · exact pair1_ns k.val hk1 h1_same
    · -- Pair 1 straddles → gap = 2
      open Finpartition in
      have hgap2 : (jg + s - j₀) % s = 2 := by
        have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
        exact straddle1_gap2 s g m hs hs3_le hs_le h_lb
          h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi hvg_lo hvg_hi hstrad1 hgap
      have hjg1_eq : (jg + 1) % 3 = j₀ % 3 := by grind [gap_mod_cases_gen]
      rcases hk1 with hk_eq | hk_eq
      · -- k = j₀%3 = (jg+1)%3: pair 2 must be non-straddle
        rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
        · exact pair2_ns k.val (Or.inr (hk_eq ▸ hjg1_eq.symm)) h2_same
        · exact absurd h1_step (both_straddle_absurd h1_step h2_step).elim
      · -- k = (j₀+1)%3: witness a = 1
        refine ⟨1, by simp, ?_⟩
        change (eqp_idx q r ((v + 1) % m) + eqp_off q r ((v + 1) % m) % 2) % 3 = k.val
        rw [straddle_boundary_color m q r s v hq_pos hr_lt hs3 hm_eq hv_lt h1_step j₀ rfl]
        exact hk_eq.symm
  · -- Pair 2 covers k: k ∈ {jg%3, (jg+1)%3}
    rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
    · exact pair2_ns k.val hk2 h2_same
    · -- Pair 2 straddles → gap = 1
      open Finpartition in
      have hgap1 : (jg + s - j₀) % s = 1 := by
        have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
        have hstrad2 : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1 :=
          endpoint_bridge ((v + g) % m) hvg_lt hjg_lt h2_step
        exact straddle2_gap1 s g m hs hs3_le hs_le h_lb
          h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi hvg_hi hstrad2 hgap
      have hj01_eq : (j₀ + 1) % 3 = jg % 3 := by grind [gap_mod_cases_gen]
      rcases hk2 with hk_eq | hk_eq
      · -- k = jg%3 = (j₀+1)%3: pair 1 must be non-straddle
        rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
        · exact pair1_ns k.val (Or.inr (hk_eq ▸ hj01_eq.symm)) h1_same
        · exact absurd h1_step (both_straddle_absurd h1_step h2_step).elim
      · -- k = (jg+1)%3: witness a = g+1
        have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
        refine ⟨g + 1, by simp, ?_⟩
        change (idx ((v + (g + 1)) % m) + off ((v + (g + 1)) % m) % 2) % 3 = k.val
        rw [vg_mod_shift m v g 1]
        change (eqp_idx q r (((v + g) % m + 1) % m) +
          eqp_off q r (((v + g) % m + 1) % m) % 2) % 3 = k.val
        rw [straddle_boundary_color m q r s ((v + g) % m)
          hq_pos hr_lt hs3 hm_eq hvg_lt h2_step jg rfl]
        exact hk_eq.symm

/-- **Key lemma (Lemma 12(iv)).** Multiplication by a unit in ZMod m is an additive
    automorphism, so it preserves HasPolychromColouring. Used throughout Case 1. -/
lemma hasPolychromColouring_mul_unit (u : (ZMod m)ˣ) (S : Finset (ZMod m)) :
    HasPolychromColouring (Fin 3) (S.image (u.val * ·)) ↔
    HasPolychromColouring (Fin 3) S := by
  have key : polychromNumber (S.image (u.val * ·)) = polychromNumber S :=
    polychromNumber_iso (AddAut.mulLeft u)
  exact ⟨fun h => hasPolychromColouring_fin_of_le (by grind) (key ▸ le_polychromNumber h),
    fun h => hasPolychromColouring_fin_of_le (by grind) (key.symm ▸ le_polychromNumber h)⟩

/-! ### Subcase (1c): per-residue lemmas (paper §4.1, case 3 ∤ m)

Each lemma below reduces `{0, 1, g, g+1}` to a translate of a Table 1 set via
multiplication by 3 (which is an automorphism of `ZMod m` when `3 ∤ m`).
The six individual `case_one_res_*` lemmas are routine; the important interface
is `case_one_residues` which dispatches to them.
-/

section Case1c

/-- m = 3g - 2: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,2,3,5}. -/
lemma case_one_res_3g_sub_2 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g - 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * (g : ZMod m) = 2 := by
    have : ((3 * g : ℕ) : ZMod m) = (m + 2 : ℕ) := by congr 1; grind
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 5 := by grind
  simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g_mod, image_singleton,
    h3g1_mod, insert_comm] using table1_0235 m (by grind)

/-- m = 3g - 1: ×3 maps {0,1,g,g+1} to {0,3,3g,3g+3} ≡ {0,1,3,4}. -/
lemma case_one_res_3g_sub_1 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g - 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = 1 := by
    have : ((3 * g : ℕ) : ZMod m) = (m + 1 : ℕ) := by congr 1; grind
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 4 := by grind
  simpa [hu, Nat.cast_ofNat, image_insert, mul_zero, mul_one, h3g_mod,
    image_singleton, h3g1_mod, insert_comm] using table1_0134 m (by grind)

/-- m = 3g + 1: ×3 maps {0,1,g,g+1} to {0,3,-1,2}, a translate of {0,1,3,4}. -/
lemma case_one_res_3g_add_1 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 1) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -1 := by
    have : ((3 * g + 1 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 2 := by grind
  have : {0, (3 : ZMod m), -1, 2} = (-1 : ZMod m) +ᵥ ({0, 1, 3, 4} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0134 m (by grind)

/-- m = 3g + 2: ×3 maps {0,1,g,g+1} to {0,3,-2,1}, a translate of {0,2,3,5}. -/
lemma case_one_res_3g_add_2 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -2 := by
    have : ((3 * g + 2 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = 1 := by grind
  have : {0, (3 : ZMod m), -2, 1} = (-2 : ZMod m) +ᵥ ({0, 2, 3, 5} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0235 m (by grind)

/-- m = 3g + 4: ×3 maps {0,1,g,g+1} to {0,3,-4,-1}, a translate of {0,3,4,7}. -/
lemma case_one_res_3g_add_4 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 4) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -4 := by
    have : ((3 * g + 4 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = -1 := by grind
  have : {0, (3 : ZMod m), -4, -1} = (-4 : ZMod m) +ᵥ ({0, 3, 4, 7} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0347 m (by grind)

/-- m = 3g + 5: ×3 maps {0,1,g,g+1} to {0,3,-5,-2}, a translate of {0,3,5,8}. -/
lemma case_one_res_3g_add_5 (g : ℕ) (hm : m ≥ 289) (hg : m = 3 * g + 5) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  obtain ⟨u, hu⟩ := ZMod.isUnit_prime_of_not_dvd Nat.prime_three (by grind : ¬3 ∣ m)
  rw [← hasPolychromColouring_mul_unit m u]
  have h3g_mod : (3 : ZMod m) * g = -5 := by
    have : ((3 * g + 5 : ℕ) : ZMod m) = (m : ℕ) := by rw [hg]
    push_cast [ZMod.natCast_self] at this
    grind
  have h3g1_mod : (3 : ZMod m) * ((g : ZMod m) + 1) = -2 := by grind
  have : {0, (3 : ZMod m), -5, -2} = (-5 : ZMod m) +ᵥ ({0, 3, 5, 8} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add]
    grind
  simpa [hu, h3g_mod, h3g1_mod, this] using table1_0358 m (by grind)

/-- **Subcase (1c) assembled:** dispatches to the six per-residue lemmas above.
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

end Case1c

/-! ### Subcase (1d): 3 ∣ m, split by g mod 3 (paper §4.1, case 3 ∣ m)

When `3 ∣ m`, multiplication by 3 is not available. Instead, explicit periodic
colorings are constructed. The three individual lemmas (`case_one_div_g_not_three`,
`case_one_div_3g`, `case_one_div_3g3`) are routine; `case_one_divisible` dispatches
to them.
-/

section Case1d

/-- (1d), g ≢ 0 (mod 3): the periodic coloring 012012...012 works because
    each translate of {0,1,g,g+1} hits all 3 residue classes mod 3. -/
lemma case_one_div_g_not_three (g : ℕ) (h_div : m = 3 * g ∨ m = 3 * g + 3)
    (hg3 : g % 3 ≠ 0) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  have h3_dvd : 3 ∣ m := by rcases h_div with rfl | rfl <;> grind
  haveI : NeZero m := ⟨by grind⟩
  apply HasPolychromColouring.of_image (ZMod.castHom h3_dvd (ZMod 3))
  simp only [Finset.image_insert, Finset.image_singleton,
    map_zero, map_one, map_add, map_natCast]
  have hg12 : g % 3 = 1 ∨ g % 3 = 2 := by grind
  suffices ({0, 1, (g : ZMod 3), (g : ZMod 3) + 1} : Finset (ZMod 3)) = Finset.univ by
    rw [this]; exact hasPolychromColouring_univ
  rcases hg12 with h | h <;> {
    have : (g : ZMod 3) = ↑(g % 3 : ℕ) := by rw [ZMod.natCast_mod]
    simp only [this, h]; decide
  }

/-- (1d), m = 3g, g ≡ 0 (mod 3): diagonal coloring `n ↦ (n%3 + n/g) % 3`. -/
lemma case_one_div_3g (g : ℕ) (hm_eq : m = 3 * g) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  let c (p : ℕ) : ℕ := (p % 3 + p / g) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c, hm_eq]
    rw [Nat.mod_mod_of_dvd p (dvd_mul_right 3 g)]
    have h2 : p = p % (3 * g) + 3 * (p / (3 * g)) * g := by grind [Nat.mod_add_div p (3 * g)]
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
    rw [ht]; grind [Nat.mul_add_mod]
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
      hcv (by grind) (by grind)
  · push_neg at hr_lt_gm1
    have hr_eq : r = g - 1 := by grind
    have hcv : c v = (2 + q) % 3 := by grind
    have hcv1 : c (v + 1) = (q + 1) % 3 := by
      have : v + 1 = g * (q + 1) + 0 := by grind
      rw [this, color_at (q + 1) 0 hg]
      grind
    have hcvg : c (v + g) = (2 + (q + 1)) % 3 := by
      have : v + g = g * (q + 1) + (g - 1) := by grind
      rw [this]
      grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)

/-- (1d), m = 3g+3, g ≡ 0 (mod 3): reversed diagonal coloring of period `g+1`. -/
lemma case_one_div_3g3 (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
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
    have hp_eq : p = h * (3 * (p / (3 * h))) + p % (3 * h) := by grind [Nat.mod_add_div p (3 * h)]
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
      have : v + g = h * (q + 1) + (g - 1) := by grind
      rw [this, color_at (q + 1) (g - 1) (by grind)]
      grind
    have hcv1 : c (v + 1) = (3 - (q + 1) % 3) % 3 := by
      have : v + 1 = h * (q + 1) + 0 := by grind
      rw [this, color_at (q + 1) 0 (by grind)]
      grind
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
      (by rw [hcv1]
          change ((r + 1) % 3 + (3 - q % 3)) % 3 = ((r % 3 + (3 - q % 3)) % 3 + 1) % 3
          omega)
      (by have : v + (g + 1) = v + g + 1 := by ring
          rw [this, hcvg1]
          change (r % 3 + (3 - (q + 1) % 3)) % 3 = ((r % 3 + (3 - q % 3)) % 3 + 2) % 3
          omega)

/-- **Subcase (1d) assembled:** dispatches on `g % 3` and `m ∈ {3g, 3g+3}` (paper §4.1). -/
lemma case_one_divisible (g : ℕ) (hm : m ≥ 289) (h_div : m = 3 * g ∨ m = 3 * g + 3) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  by_cases hg3 : g % 3 = 0
  · rcases h_div with h | h
    · exact case_one_div_3g m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
    · exact case_one_div_3g3 m g h (Nat.dvd_of_mod_eq_zero hg3) (by grind)
  · exact case_one_div_g_not_three m g h_div hg3

end Case1d

/-! ### Combined dispatch for Case 1 -/

/-- **Case 1 combined dispatch:** applies subcases (1a)–(1d) for 2 ≤ g ≤ m/2 and m ≥ 289.
    This is the main lemma for the single-cycle case, assuming the set has already been
    reduced to the form {0, 1, g, g+1}. -/
lemma case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g) (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
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
        exact case_one_interval m 3 g (by grind) ⟨1, rfl⟩ (by grind) (by grind : g < 2 * (m / 3))
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
          by_contra! hlt
          exact absurd ((Nat.div_lt_iff_lt_mul h3g1).mp hlt) (by grind)
        have hq_ub : m - 1 < 3 * (g - 1) * (q + 1) := Nat.lt_mul_div_succ _ h3g1
        have hm_lb : m ≥ q * (3 * (g - 1)) + 1 := by grind
        exact case_one_interval m (3 * (q + 1)) g (by grind) ⟨q + 1, rfl⟩ (by -- ⌈m/s⌉ < g
            rw [Nat.div_lt_iff_lt_mul (by grind)]
            have : g * (3 * (q + 1)) = (g - 1 + 1) * (3 * (q + 1)) := by grind
            grind)
          (by -- g < 2⌊m/s⌋
            suffices h : (g + 2) / 2 ≤ m / (3 * (q + 1)) by grind
            rw [Nat.le_div_iff_mul_le (by grind)]
            suffices (g + 2) * (3 * (q + 1)) ≤ 2 * m by
              have := Nat.div_mul_le_self (g + 2) 2; nlinarith
            by_cases hg10 : g ≥ 10
            · have : g ≥ 1 := by grind
              zify [this] at hm_lb ⊢; nlinarith
            · have : g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 := by grind
              rcases this with rfl | rfl | rfl | rfl | rfl <;> grind)

/-! ### WLOG and aggregation lemmas for Case 1 -/

/-- Auxiliary: WLOG g ≤ m/2, since {0,1,m-g,m-g+1} = (-g) +ᵥ {0,1,g,g+1}. -/
lemma case_one_complement (g : ℕ) (hg : g < m) : HasPolychromColouring (Fin 3)
      ({0, 1, (↑(m - g) : ZMod m), (↑(m - g) : ZMod m) + 1} : Finset (ZMod m)) ↔
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  have key : (↑(m - g) : ZMod m) = -(↑g : ZMod m) := by
    rw [Nat.cast_sub hg.le, ZMod.natCast_self, zero_sub]
  have hset : ({0, 1, -(↑g : ZMod m), -(↑g : ZMod m) + 1} : Finset (ZMod m)) =
      (-(↑g : ZMod m)) +ᵥ ({0, 1, (↑g : ZMod m), (↑g : ZMod m) + 1} : Finset (ZMod m)) := by
    simp only [vadd_finset_insert, vadd_finset_singleton, vadd_eq_add, neg_add_cancel]
    grind
  rw [key, hset]
  exact hasPolychromColouring_vadd


/-- **Key reduction for Case 1.** When gcd(b, m) = 1, finds the gap parameter g
    such that zmod_set m a b = (image of {0,1,g,g+1} under ×b). -/
lemma exists_g_of_coprime (a b : ℤ) (hd : Nat.gcd b.natAbs m = 1)
    (hm : 0 < m) (hcard : (zmod_set m a b).card = 4) :
    ∃ g : ℕ, 2 ≤ g ∧ g ≤ m - 2 ∧ zmod_set m a b =
        ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)).image ((b : ZMod m) * ·) := by
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
  have hbg'1 : bz * (g' + 1) = 2 * bz - az := by rw [mul_add, mul_one, hbg']; ring
  have hset : zmod_set m a b = ({0, 1, g', g' + 1} : Finset (ZMod m)).image (bz * ·) := by
    simp only [zmod_set, Finset.image_insert, Finset.image_singleton]
    simp only [mul_zero, mul_one, hbg', hbg'1]
    grind
  have hval : (g'.val : ZMod m) = g' := ZMod.natCast_zmod_val g'
  have hinj : Function.Injective (bz * · : ZMod m → ZMod m) := fun x y h => by
    simpa [← mul_assoc, ZMod.inv_mul_of_unit _ hub] using congr_arg (bz⁻¹ * ·) h
  have hcard4 : ({0, 1, g', g' + 1} : Finset (ZMod m)).card = 4 := by
    rwa [hset, Finset.card_image_of_injective _ hinj] at hcard
  refine ⟨g'.val, ?_, ?_, ?_⟩
  · by_contra! hlt
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
  · by_contra! hgt
    have hval_lt := ZMod.val_lt g'
    have hgm1 : g'.val = m - 1 := by grind
    have hg'p1 : g' + 1 = 0 := by
      rw [← hval, hgm1, Nat.cast_sub (by grind), Nat.cast_one, ZMod.natCast_self, zero_sub,
        neg_add_cancel]
    have hsub : ({0, 1, g', g' + 1} : Finset (ZMod m)) ⊆ {0, 1, g'} := by grind
    grind [Finset.card_le_card hsub, Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := g')]
  · conv at hset => rhs; rw [← hval]
    exact hset

/-- **Main Case 1 (Single Cycle).** Aggregates all subcases (1a)–(1d).
    Reduces to {0,1,g,g+1} via `exists_g_of_coprime`, applies WLOG g ≤ m/2,
    then dispatches via `case_one_dispatch`. -/
lemma main_case_one (a b : ℤ) (hm : m ≥ 289) (hcard : (zmod_set m a b).card = 4)
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
  rw [hset, ← hu, hasPolychromColouring_mul_unit]
  by_cases hg_half : g ≤ m / 2
  · exact case_one_dispatch m g hm hg_ge hg_half
  · push_neg at hg_half
    rw [← case_one_complement m g (by grind)]
    exact case_one_dispatch m (m - g) hm (by grind) (by grind)

end Case1_SingleCycle
