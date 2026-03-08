import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Scratch file 2: Key lemmas for case_one_interval
-/

private lemma lt_two (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 := by omega

section helpers

lemma two_pairs_cover (j₁ j₂ : ℕ) (hne : j₁ % 3 ≠ j₂ % 3)
    (k : ℕ) (hk : k < 3) :
    k = j₁ % 3 ∨ k = (j₁ + 1) % 3 ∨ k = j₂ % 3 ∨ k = (j₂ + 1) % 3 := by
  have : j₁ % 3 = 0 ∨ j₁ % 3 = 1 ∨ j₁ % 3 = 2 := by omega
  have : j₂ % 3 = 0 ∨ j₂ % 3 = 1 ∨ j₂ % 3 = 2 := by omega
  have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases ‹j₁ % 3 = 0 ∨ _› with h1 | h1 | h1 <;>
  rcases ‹j₂ % 3 = 0 ∨ _› with h2 | h2 | h2 <;>
  rcases ‹k = 0 ∨ _› with hk' | hk' | hk' <;> simp_all <;> omega

/-- Phase differs when gap is 1 or 2 mod s, and 3 | s. -/
lemma phase_ne_of_gap {s j₀ jg : ℕ} (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by
  obtain ⟨t, ht⟩ := hs3; subst ht
  have ht_pos : 0 < t := by omega
  -- Bound quotient of (jg + 3t - j₀) / (3t): it's 0 or 1
  have h3t_pos : 0 < 3 * t := by omega
  have hqlt : (jg + 3 * t - j₀) / (3 * t) < 2 := by
    rw [Nat.div_lt_iff_lt_mul h3t_pos]; omega
  have hdam := Nat.div_add_mod (jg + 3 * t - j₀) (3 * t)
  rcases hgap with hmod | hmod <;> rcases lt_two _ hqlt with hq | hq <;>
    rw [hq, hmod] at hdam <;> simp at hdam
  · -- gap ≡ 1 (mod 3t), quotient = 0: jg + 3t - j₀ = 1
    have : j₀ = 3 * t - 1 := by omega
    have : jg = 0 := by omega
    rw [‹jg = 0›, ‹j₀ = 3 * t - 1›]
    have h3t1 : 3 * t - 1 = 3 * (t - 1) + 2 := by omega
    rw [h3t1, Nat.mul_add_mod]; omega
  · -- gap ≡ 1 (mod 3t), quotient = 1: jg = j₀ + 1
    have : jg = j₀ + 1 := by omega
    rw [this]; omega
  · -- gap ≡ 2 (mod 3t), quotient = 0: jg + 3t - j₀ = 2
    by_cases hj₀ : j₀ = 3 * t - 1
    · have : jg = 1 := by omega
      rw [this, hj₀]
      have h3t1 : 3 * t - 1 = 3 * (t - 1) + 2 := by omega
      rw [h3t1, Nat.mul_add_mod]; omega
    · have : j₀ = 3 * t - 2 := by omega
      have : jg = 0 := by omega
      rw [‹jg = 0›, ‹j₀ = 3 * t - 2›]
      have h3t2 : 3 * t - 2 = 3 * (t - 1) + 1 := by omega
      rw [h3t2, Nat.mul_add_mod]; omega
  · -- gap ≡ 2 (mod 3t), quotient = 1: jg = j₀ + 2
    have : jg = j₀ + 2 := by omega
    rw [this]; omega

end helpers

/-! ## Sorry'd lemmas -/

-- Sorry 1: gap bound
lemma gap_bound (s g m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) :
    let bd := (m % s) * (m / s + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (m / s + 1)
      else m % s + (p - bd) / (m / s)
    let j₀ := idx v
    let jg := idx ((v + g) % m)
    (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2 := by
  sorry

-- idx range: idx(p) < s for p < m
lemma idx_lt_s (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
    (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let idx := if p < bd then p / (q + 1) else r + (p - bd) / q
    idx < s := by
  simp only
  set q := m / s; set r := m % s; set bd := r * (q + 1)
  have hq_pos : 0 < q := Nat.div_pos hs_le hs
  have hr_lt : r < s := Nat.mod_lt m hs
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hbd_eq : bd + (s - r) * q = m := by
    have h1 : bd = r * q + r := by ring
    have h2 : (s - r) * q + r * q = s * q := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
    linarith
  split
  · rename_i hlt
    have : p / (q + 1) < r := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)]; exact hlt
    omega
  · rename_i hge
    push_neg at hge
    have : (p - bd) / q < s - r := by
      rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
    omega

/-! ## The main coverage lemma -/

/-- The core coverage lemma for case_one_interval.
    For every v < m and k < 3, some a ∈ {0,1,g,g+1} gives c(v+a) = k. -/
lemma case_one_interval_core
    (s g m : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (v : ℕ) (hv_lt : v < m) (k : ℕ) (hk : k < 3) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let idx (p : ℕ) : ℕ :=
      if p < bd then p / (q + 1) else r + (p - bd) / q
    let off (p : ℕ) : ℕ :=
      if p < bd then p % (q + 1) else (p - bd) % q
    let c (p : ℕ) : ℕ := (idx (p % m) + off (p % m) % 2) % 3
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = k := by
  intro q r bd idx off c
  -- c(p) ∈ {idx(p%m)%3, (idx(p%m)+1)%3}
  have hc_phase : ∀ p, c p = idx (p % m) % 3 ∨
      c p = (idx (p % m) + 1) % 3 := by
    intro p; simp only [c]
    have : off (p % m) % 2 = 0 ∨ off (p % m) % 2 = 1 := by omega
    rcases this with h | h <;> simp [h] <;> omega
  -- Phase difference from gap bound
  set j₀ := idx v with hj₀_def
  set jg := idx ((v + g) % m) with hjg_def
  have hgap := gap_bound s g m hs hs_le h_lb h_ub v hv_lt
  -- idx ranges
  have hj₀_lt : j₀ < s :=
    idx_lt_s s m hs hs_le v hv_lt
  have hjg_lt : jg < s :=
    idx_lt_s s m hs hs_le ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Phase difference: j₀ % 3 ≠ jg % 3
  have hphase : j₀ % 3 ≠ jg % 3 :=
    phase_ne_of_gap hs3 hj₀_lt hjg_lt hgap
  -- From two_pairs_cover: k is one of {j₀%3, (j₀+1)%3, jg%3, (jg+1)%3}
  have hk_in := two_pairs_cover j₀ jg hphase k hk
  -- Sorry 2a: pair 1 covers both j₀-phases
  have hpair1_cover : ∀ t < 3,
      t = j₀ % 3 ∨ t = (j₀ + 1) % 3 →
      (∃ a ∈ ({0, 1} : Finset ℕ), c (v + a) = t) := by sorry
  -- Sorry 2b: pair 2 covers both jg-phases
  have hpair2_cover : ∀ t < 3,
      t = jg % 3 ∨ t = (jg + 1) % 3 →
      (∃ a ∈ ({g, g + 1} : Finset ℕ), c (v + a) = t) := by sorry
  -- Dispatch: for each case of two_pairs_cover, find witness in {0,1,g,g+1}
  rcases hk_in with hk1 | hk2 | hk3 | hk4
  · obtain ⟨a, ha, hca⟩ := hpair1_cover k hk (Or.inl hk1)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    exact ⟨a, by rcases ha with rfl | rfl <;> simp, hca⟩
  · obtain ⟨a, ha, hca⟩ := hpair1_cover k hk (Or.inr hk2)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    exact ⟨a, by rcases ha with rfl | rfl <;> simp, hca⟩
  · obtain ⟨a, ha, hca⟩ := hpair2_cover k hk (Or.inl hk3)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    exact ⟨a, by rcases ha with rfl | rfl <;> simp, hca⟩
  · obtain ⟨a, ha, hca⟩ := hpair2_cover k hk (Or.inr hk4)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    exact ⟨a, by rcases ha with rfl | rfl <;> simp, hca⟩
