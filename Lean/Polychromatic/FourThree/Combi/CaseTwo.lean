import Polychromatic.FourThree.Combi.BlockColour

open Finset Pointwise

/-! ## Main Case 2: Multiple Cycles (paper §4.2)

When both $d_1 = \gcd(b, m) > 1$ and $d_2 = \gcd(b-a, m) > 1$, the action of $b$ on
$\mathbb{Z}_m$ decomposes into $d_1$ cycles of length $e_1 = m/d_1$.
We use the isomorphism $\mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \cong \mathbb{Z}_m$ to define
coordinate-based colorings.

Specifically, the "orbit map" $\phi(i, j) = i(b-a) + jb \pmod m$ provides a coordinate system
where moving by $b$ corresponds to $(i, j) \to (i, j+1)$ and moving by $(b-a)$ corresponds
to $(i, j) \to (i+1, j')$. Each translate of $S$ thus touches two adjacent cycles and two
consecutive positions within each cycle.

The proof splits into subcases based on the parity of $d_1$ and $e_1$:
- **(2a) $e_1$ even:**
  Each cycle uses two alternating colors; adjacent cycles skip different colors.
- **(2b) $d_1$ even, $e_1$ odd:** Similar but with special "degenerate" handling for odd lengths.
- **(2c) Both odd, $e_1 \le 17$:** Shifted periodic colorings.
- **(2d) Both odd, $e_1 \ge 19$:** Rotating patterns based on a 3-interval partition.
-/

section Case2_MultipleCycles

variable (m : ℕ) (a b : ℤ)

/-! ### Arithmetic helpers for cycle decomposition -/

private lemma intCast_2ba_eq :
    ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by
  grind

private lemma ZMod.val_add_one {n : ℕ} [NeZero n] (x : ZMod n) : (x + 1).val = (x.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

private lemma zmod_val_add_one (d : ℕ) [NeZero d] (_hd : d ≥ 2) (i : ZMod d) :
    (i + 1).val = if i.val + 1 < d then i.val + 1 else 0 := by
  rw [ZMod.val_add_one]; split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · grind [Nat.mod_self]

private lemma parity_flip_even (e : ℕ) [NeZero e] (he : Even e) (he2 : e ≥ 2)
    (j : ZMod e) : j.val % 2 ≠ (j + 1).val % 2 := by
  grind [zmod_val_add_one e he2 j]

/-- Coloring for Case 2a ($e_1$ even): alternating bicolors per cycle,
    missing colors chosen so adjacent cycles skip different colors. -/
private def cycle_coloring (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
  if i.val = d₁ - 1 ∧ ¬Even d₁ then ⟨1 + j.val % 2, by grind⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by grind⟩
  else ⟨2 * (j.val % 2), by grind⟩

-- Coverage: adjacent cycles cover all 3 colors.
private lemma color_covers_even (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (hd₁_ge2 : d₁ ≥ 2)
    (hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d₁) (j₁ j₂ : ZMod e₁) (k : Fin 3) :
    k = cycle_coloring d₁ e₁ (i, j₁) ∨
    k = cycle_coloring d₁ e₁ (i, j₁ + 1) ∨
    k = cycle_coloring d₁ e₁ (i + 1, j₂) ∨
    k = cycle_coloring d₁ e₁ (i + 1, j₂ + 1) := by
  grind [cycle_coloring, Fin.ext_iff, zmod_val_add_one]

/-- Orbit map $\phi(i, j) = i(b-a) + jb \pmod m$, a bijection
    $\mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \to \mathbb{Z}_m$. -/
private def orbitMap (m : ℕ) (a b : ℤ) (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b

private lemma addOrderOf_b_eq {m : ℕ} {b : ℤ} {d₁ : ℕ} (hm : 0 < m)
    (hd1_def : Nat.gcd b.natAbs m = d₁) :
    addOrderOf (b : ZMod m) = m / d₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = m / d₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (by grind), Nat.gcd_comm, hd1_def]
  rcases Int.natAbs_eq b with h | h
  · have : (b : ZMod m) = (b.natAbs : ZMod m) := by rw [h]; simp
    grind
  · have : (b : ZMod m) = -(b.natAbs : ZMod m) := by rw [h]; simp
    rw [this, addOrderOf_neg]; exact key

private lemma b_zero_mod_d1 {m : ℕ} {b : ℤ} {d₁ : ℕ}
    (hd1_def : Nat.gcd b.natAbs m = d₁) [NeZero d₁] :
    (b : ZMod d₁) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natCast_dvd.mpr (hd1_def ▸ Nat.gcd_dvd_left b.natAbs m)

private lemma ba_coprime_d1 {m : ℕ} {a b : ℤ} {d₁ : ℕ}
    (hd1_dvd : d₁ ∣ m)
    (h_gcd_coprime : d₁.gcd (Nat.gcd (b - a).natAbs m) = 1) :
    Nat.Coprime (b - a).natAbs d₁ :=
  Nat.dvd_one.mp (h_gcd_coprime ▸ Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_right _ _) hd1_dvd)))

private lemma orbitMap_i_eq {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    {i₁ i₂ : ZMod d₁} {j₁ j₂ : ZMod e₁}
    (heq : orbitMap m a b d₁ e₁ (i₁, j₁) = orbitMap m a b d₁ e₁ (i₂, j₂)) :
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
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by grind [j₁.val_lt (n := e₁), j₂.val_lt (n := e₁)])
    exact ZMod.val_injective _ (by grind)

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
    grind
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
      orbitMap m a b d₁ e₁ p + (b : ZMod m) = orbitMap m a b d₁ e₁ (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by
      rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]
    grind
  · have hje : j.val + 1 = e₁ := by grind [ZMod.val_lt]
    have hv : (j + 1).val = 0 := by rw [ZMod.val_add_one, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      have : (j.val : ZMod m) * ↑b + ↑b = (j.val + 1 : ℕ) • (b : ZMod m) := by
        rw [add_nsmul, one_nsmul, nsmul_eq_mul]
      rw [this, hje, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]

private lemma orbitMap_shift_ba {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ} [NeZero d₁]
    (i : ZMod d₁) (j : ZMod e₁)
    (hi : i.val + 1 < d₁) :
    orbitMap m a b d₁ e₁ (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b d₁ e₁ (i + 1, j) := by
  simp only [orbitMap]
  have : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
  rw [this]
  grind

/-- The cycle index α(x) = castHom(x) * u⁻¹ satisfies α(φ(i,j)) = i. -/
private lemma orbitMap_cycle_index {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁))
    (i : ZMod d₁) (j : ZMod e₁) :
    ZMod.castHom hd1_dvd (ZMod d₁) (orbitMap m a b d₁ e₁ (i, j)) * u⁻¹ = i := by
  simp only [orbitMap]
  rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast,
    map_intCast, hb_zero, mul_zero, add_zero, mul_assoc,
    ← hu, u.mul_inv, mul_one]
  simp [ZMod.natCast_val]

/-- The cycle index α shifts by 1 when (b-a) is added. -/
private lemma cycle_index_shift_ba {m : ℕ} {a b : ℤ} {d₁ : ℕ}
    [NeZero m] [NeZero d₁]
    (hd1_dvd : d₁ ∣ m)
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁))
    (x : ZMod m) :
    ZMod.castHom hd1_dvd (ZMod d₁) (x + ↑(b - a)) * u⁻¹ =
    ZMod.castHom hd1_dvd (ZMod d₁) x * u⁻¹ + 1 := by
  simp only [map_add, map_intCast, add_mul]
  rw [← hu]; ring_nf; rw [u.inv_mul]; ring

/-- If Φ(i, j+1) = Φ(i, j) + b, then Φ⁻¹(x+b) = (same_i, j+1). -/
private lemma equiv_symm_shift_b {d₁ e₁ : ℕ} {γ : Type*} [AddCommMonoid γ]
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) {b : γ}
    (hΦ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, Φ (i, j + 1) = Φ (i, j) + b)
    (x : γ) :
    Φ.symm (x + b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := by
  grind

/-- If α(Φ(i,j)) = i for all i,j, then (Φ⁻¹(x)).1 = α(x). -/
private lemma equiv_symm_fst_eq {d₁ e₁ : ℕ} {γ : Type*}
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) (α : γ → ZMod d₁)
    (hα : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (Φ (i, j)) = i)
    (x : γ) :
    (Φ.symm x).1 = α x := by
  grind

/-! ### Orbit coloring framework -/

/-- **Key infrastructure for Case 2.** Polychromaticity from an orbit coloring. -/
private lemma orbit_coloring_polychrom {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (Φ : ZMod d₁ × ZMod e₁ ≃ ZMod m)
    (hΦ_add_b : ∀ x : ZMod m, Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1))
    (hΦ_cycle_shift : ∀ x : ZMod m, (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1)
    (f : ZMod d₁ × ZMod e₁ → Fin 3)
    (hcovers : ∀ (n : ZMod m) (k : Fin 3),
      k = f ((Φ.symm n).1, (Φ.symm n).2) ∨
      k = f ((Φ.symm n).1, (Φ.symm n).2 + 1) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2 + 1)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  let χ : ZMod m → Fin 3 := f ∘ Φ.symm
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set i := (Φ.symm n).1; set j := (Φ.symm n).2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := congr_arg f (hΦ_add_b n)
  have hi_shift : (Φ.symm (n + ↑(b - a))).1 = i + 1 := hΦ_cycle_shift n
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') := congr_arg f (Prod.ext hi_shift rfl)
  have hχ_n2ba : χ (n + ↑(2 * b - a)) = f (i + 1, j' + 1) := by
    have : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by rw [intCast_2ba_eq, add_assoc]
    grind
  rcases hcovers n k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  · grind
  · grind
  · grind

/-! ### Subcase (2a): e₁ even -/

/-- **Subcase (2a).** $e_1$ is even. Each cycle uses two alternating colors;
    adjacent cycles skip different colors. The simplest of the four subcases. -/
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
    have : 0 < e₁ := Nat.div_pos (Nat.le_of_dvd (by grind) hd₁_dvd) (by grind)
    grind
  haveI : NeZero m := ⟨by grind⟩
  haveI : NeZero d₁ := ⟨by grind⟩
  haveI : NeZero e₁ := ⟨by grind⟩
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := b_zero_mod_d1 rfl
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 hd₁_dvd h_gcd_coprime)
  -- addOrderOf b in ZMod m is e₁
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by grind) rfl
  have he1_b : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  -- Define the cycle map φ = orbitMap and derive bijectivity from shared infrastructure
  let φ := orbitMap m a b d₁ e₁
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; exact (orbitMap_shift_b he1_b (i, j)).symm
  -- φ is bijective (from shared orbitMap infrastructure)
  let Φ := Equiv.ofBijective φ (orbitMap_bijective hm_eq hd₁_dvd hb_zero hba_unit hord)
  -- Cycle index function α : ZMod m → ZMod d₁
  obtain ⟨u_ba, hu_ba⟩ := hba_unit
  let α : ZMod m → ZMod d₁ := fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
  have hα_ba : ∀ x, α (x + ↑(b - a)) = α x + 1 := cycle_index_shift_ba hd₁_dvd u_ba hu_ba
  have hα_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (φ (i, j)) = i :=
    orbitMap_cycle_index hd₁_dvd hb_zero u_ba hu_ba
  have hΦ_add_b := equiv_symm_shift_b Φ hφ_add_b
  have hΦ_cycle := equiv_symm_fst_eq Φ α hα_φ
  have hd₁_ge2 : d₁ ≥ 2 := by grind
  have hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2 := parity_flip_even e₁ he1_even he₁_ge2
  exact orbit_coloring_polychrom Φ hΦ_add_b
    (fun x => by rw [hΦ_cycle, hα_ba, ← hΦ_cycle])
    (cycle_coloring d₁ e₁)
    (fun n k => color_covers_even d₁ e₁ hd₁_ge2 hparity _ _ _ k)

/-! ### Subcase (2b) construction: d₁ even, e₁ odd -/

-- Case 2b coloring: even cycles `01010…011`, odd cycles `22020…020`.
private def case2b_coloring (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
  if i.val % 2 = 0 then  -- even cycle
    if j.val = e₁ - 1 then 1
    else if j.val % 2 = 0 then 0
    else 1
  else  -- odd cycle
    if j.val = 0 then 2
    else if j.val % 2 = 0 then 0
    else 2

-- Coverage — any 2×2 block covers all 3 colors.
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
  grind [case2b_coloring, Fin.ext_iff, zmod_val_add_one, parity_flip_even]

/-! ### Subcase (2b) main lemma -/

/-- **Subcase (2b).** $d_1$ even, $e_1$ odd: alternating with degenerate fixup. -/
lemma case_two_d1_even_e1_odd (hm : m ≥ 289)
    (h_gcd_coprime : (Nat.gcd b.natAbs m).gcd (Nat.gcd (b - a).natAbs m) = 1)
    (h_min : min (Nat.gcd b.natAbs m) (Nat.gcd (b - a).natAbs m) > 1)
    (hd1_even : Even (Nat.gcd b.natAbs m))
    (he1_odd : Odd (m / Nat.gcd b.natAbs m)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  set d₁ := Nat.gcd b.natAbs m with hd₁_def
  set e₁ := m / d₁ with he₁_def
  have hd₁_dvd : d₁ ∣ m := Nat.gcd_dvd_right _ _
  have hd₁_pos : 0 < d₁ := Nat.pos_of_ne_zero (by grind)
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd₁_dvd).symm
  -- e₁ ≥ 3: e₁ is odd and e₁ = 1 would give d₁ = m, contradicting gcd(d₁,d₂) = 1
  have he₁_pos : 0 < e₁ := Nat.div_pos (Nat.le_of_dvd (by grind) hd₁_dvd) hd₁_pos
  have he₁_ge3 : e₁ ≥ 3 := by
    by_contra! h
    rcases (by grind : e₁ = 1 ∨ e₁ = 2) with he | he
    · have hba_dvd_d₁ : Nat.gcd (b - a).natAbs m ∣ d₁ := by
        rw [hm_eq, he, mul_one]; exact Nat.gcd_dvd_right _ _
      have : Nat.gcd (b - a).natAbs m = 1 :=
        Nat.eq_one_of_dvd_one (h_gcd_coprime ▸ Nat.dvd_gcd hba_dvd_d₁ (dvd_refl _))
      grind
    · grind
  haveI : NeZero m := ⟨by grind⟩
  haveI : NeZero d₁ := ⟨by grind⟩
  haveI : NeZero e₁ := ⟨by grind⟩
  have hb_zero : (Int.cast b : ZMod d₁) = 0 := b_zero_mod_d1 rfl
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 hd₁_dvd h_gcd_coprime)
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by grind) rfl
  have he1_b : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  -- b/d₁ is coprime to e₁ (needed for compatibility argument)
  have hd₁_dvd_b : (d₁ : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero
  obtain ⟨q, hq⟩ := hd₁_dvd_b
  have hq_cop : Nat.Coprime q.natAbs e₁ := by
    rw [show q.natAbs = b.natAbs / d₁ from by
      rw [hq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hd₁_pos]]
    exact Nat.coprime_div_gcd_div_gcd hd₁_pos
  -- Define the cycle map φ = orbitMap and derive bijectivity from shared infrastructure
  let φ := orbitMap m a b d₁ e₁
  let Φ := Equiv.ofBijective φ (orbitMap_bijective hm_eq hd₁_dvd hb_zero hba_unit hord)
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; exact (orbitMap_shift_b he1_b (i, j)).symm
  -- Cycle index function α : ZMod m → ZMod d₁
  obtain ⟨u_ba, hu_ba⟩ := hba_unit
  let α : ZMod m → ZMod d₁ := fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
  have hα_ba : ∀ x, α (x + ↑(b - a)) = α x + 1 := cycle_index_shift_ba hd₁_dvd u_ba hu_ba
  have hα_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (φ (i, j)) = i :=
    orbitMap_cycle_index hd₁_dvd hb_zero u_ba hu_ba
  have hΦ_add_b := equiv_symm_shift_b Φ hφ_add_b
  have hΦ_cycle := equiv_symm_fst_eq Φ α hα_φ
  -- d₂ properties for the compatibility argument
  set d₂ := Nat.gcd (b - a).natAbs m
  have hd₂_dvd : d₂ ∣ m := Nat.gcd_dvd_right _ _
  have hd₂_gt1 : d₂ > 1 := by grind
  have hd₂_dvd_ba : (d₂ : ℤ) ∣ (b - a) := by
    simpa [Int.gcd, d₂] using Int.gcd_dvd_left (b - a) (m : ℤ)
  have hd₂_dvd_e₁ : d₂ ∣ e₁ := by
    have h1 : d₂ ∣ d₁ * e₁ := hm_eq ▸ hd₂_dvd
    have h2 : Nat.Coprime d₂ d₁ := by rwa [Nat.Coprime, Nat.gcd_comm]
    exact h2.dvd_of_dvd_mul_right (mul_comm d₁ e₁ ▸ h1)
  -- Projection: π(φ(i,j)) = j.val * π(b) since π(b-a) = 0
  haveI : NeZero d₂ := ⟨by grind⟩
  let π : ZMod m → ZMod d₂ := ZMod.castHom hd₂_dvd (ZMod d₂)
  have hπ_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      π (φ (i, j)) = (j.val : ZMod d₂) * π (↑b) := by
    intro i j; simp only [φ, orbitMap, π, map_add, map_mul, map_natCast, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba]; ring
  have hπ_b_unit : IsUnit (π (↑b)) := by
    change IsUnit ((ZMod.castHom hd₂_dvd (ZMod d₂)) (↑b))
    rw [map_intCast]; exact isUnit_intCast_of_natAbs_coprime (by grind)
  -- Degenerate positions can't coincide: d₂ | (j-j') from projection,
  -- d₂ | e₁ and d₂ > 1, so e₁-2 and 0 can't both be 0 mod d₂.
  have h_degenerate_false : ∀ (j₁ j₂ : ZMod e₁),
      (j₁.val : ZMod d₂) * π (↑b) = (j₂.val : ZMod d₂) * π (↑b) →
      j₁.val = 0 → j₂.val = e₁ - 2 → False := by
    intro j₁ j₂ heq hj₁ hj₂
    have hval_eq := hπ_b_unit.mul_right_cancel heq
    rw [hj₁, hj₂, Nat.cast_zero] at hval_eq
    have hd₂_dvd_diff := (ZMod.natCast_eq_zero_iff _ _).mp hval_eq.symm
    have hd₂_dvd_2 : d₂ ∣ 2 := by
      have h := Nat.dvd_sub hd₂_dvd_e₁ hd₂_dvd_diff
      rwa [show e₁ - (e₁ - 2) = 2 from by grind] at h
    obtain ⟨_, hk⟩ := hd₂_dvd_e₁; obtain ⟨_, hl⟩ := he1_odd
    have := Nat.le_of_dvd (by grind) hd₂_dvd_2; grind
  -- Define coloring and prove polychromaticity via orbit helper
  have hΦ_cycle_shift : ∀ x : ZMod m,
      (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1 := fun x => by
    rw [hΦ_cycle, hα_ba, ← hΦ_cycle]
  -- π(n) and π(n+(b-a)) give the same ZMod d₂ value
  have hπ_eq : ∀ n : ZMod m, π (n + ↑(b - a)) = π n := fun n => by
    simp only [π, map_add, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba, add_zero]
  exact orbit_coloring_polychrom Φ hΦ_add_b hΦ_cycle_shift (case2b_coloring d₁ e₁) (fun n k => by
      set p := Φ.symm n; set j := p.2
      set j' := (Φ.symm (n + ↑(b - a))).2
      have hπn : π n = (j.val : ZMod d₂) * π (↑b) := by
        have : n = Φ p := (Equiv.apply_symm_apply Φ n).symm
        grind
      have hπn' : π n = (j'.val : ZMod d₂) * π (↑b) := by
        rw [← hπ_eq]
        have : n + ↑(b - a) = Φ (Φ.symm (n + ↑(b - a))) := (Equiv.apply_symm_apply Φ _).symm
        grind
      have hπ_jj' := hπn.symm.trans hπn'
      exact case2b_coverage_gen d₁ e₁ hd1_even he1_odd he₁_ge3 _ j j'
        (fun hj hj' => h_degenerate_false j j' hπ_jj' hj hj')
        (fun hj' hj => h_degenerate_false j' j hπ_jj'.symm hj' hj) k)

-- Pattern assignment for Case 2c, parametrized by k₀ (the wrap shift).
-- Variant A (k₀ % 3 ≠ 2): even→0, odd→1, last→2.
-- Variant B (k₀ % 3 = 2): even→0, odd→2, last→1.
private def case2c_pattern (d₁ k₀ i : ℕ) : Fin 3 :=
  if i = d₁ - 1 ∧ d₁ % 2 = 1 then
    if k₀ % 3 = 2 then 1 else 2
  else if i % 2 = 0 then 0
  else if k₀ % 3 = 2 then 2 else 1

-- General coverage: if (j₁ + p₁) % 3 ≠ (j₂ + p₂) % 3, all 3 colors appear.
private lemma cover_mod3_general (p₁ p₂ : Fin 3)
    (j₁ j₂ : ℕ)
    (hne : (j₁ + p₁.val) % 3 ≠ (j₂ + p₂.val) % 3)
    (k : Fin 3) :
    k = ⟨(j₁ + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₁ + 1 + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + 1 + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ := by
  by_contra! hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  grind [Fin.ext_iff]

-- Non-wrap coverage hypothesis: j₁ = j₂, patterns differ → hypothesis holds.
private lemma case2c_nonwrap_hyp (d₁ k₀ i j : ℕ) (hd₁ : d₁ ≥ 3)
    (hd₁_odd : Odd d₁) (hi : i + 1 < d₁) :
    (j + (case2c_pattern d₁ k₀ i).val) % 3 ≠
    (j + (case2c_pattern d₁ k₀ (i + 1)).val) % 3 := by
  obtain ⟨k, hk⟩ := hd₁_odd; subst hk
  grind [case2c_pattern]

-- Wrap coverage hypothesis: j₂ = j₁ + k₀, pattern chosen to avoid conflict.
private lemma case2c_wrap_hyp (d₁ k₀ j : ℕ) (hd₁ : d₁ ≥ 3)
    (hd₁_odd : Odd d₁) :
    (j + (case2c_pattern d₁ k₀ (d₁ - 1)).val) % 3 ≠
    (j + k₀ + (case2c_pattern d₁ k₀ 0).val) % 3 := by
  obtain ⟨k, hk⟩ := hd₁_odd; subst hk
  grind [case2c_pattern]

/-! ### Subcase (2d): d₁, e₁ both odd, e₁ ≥ 19 -/

/-- First interval size: u = e₁/3 + e₁%3. -/
private def case2d_u (e₁ : ℕ) : ℕ := e₁ / 3 + e₁ % 3

/-- Second interval size: v = e₁/3 + (1 if e₁%3=1 else 0). -/
private def case2d_v (e₁ : ℕ) : ℕ :=
  if e₁ % 3 = 1 then e₁ / 3 + 1 else e₁ / 3

private lemma case2d_uv_le {e₁ : ℕ} (hge : e₁ ≥ 19) : case2d_u e₁ + case2d_v e₁ ≤ e₁ := by
  grind [case2d_u, case2d_v]

/-- Base pattern: three alternating bicolor intervals {01…0, 12…1, 20…2}. -/
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

/-- For any j, {basePattern(j), basePattern(j+1 mod e₁)} covers the
    interval pair of whichInterval(j). -/
private lemma basePattern_consec_pair {e₁ j : ℕ}
    (he : Odd e₁) (hge : e₁ ≥ 19) (hj : j < e₁) :
    intervalColors (whichInterval e₁ j) ⊆ {basePattern e₁ j, basePattern e₁ ((j + 1) % e₁)} := by
  obtain ⟨ku, hku⟩ : Odd (case2d_u e₁) := by obtain ⟨k, hk⟩ := he; grind [case2d_u]
  obtain ⟨kv, hkv⟩ : Odd (case2d_v e₁) := by obtain ⟨k, hk⟩ := he; grind [case2d_v]
  obtain ⟨kw, hkw⟩ : Odd (e₁ - case2d_u e₁ - case2d_v e₁) := by
    obtain ⟨k, hk⟩ := he; grind [case2d_u, case2d_v]
  have huv := case2d_uv_le hge
  by_cases hj1 : j + 1 < e₁
  · rw [Nat.mod_eq_of_lt hj1]
    by_cases hsame : whichInterval e₁ j = whichInterval e₁ (j + 1)
    · -- Same interval: both colors present
      exact (show {basePattern e₁ j, basePattern e₁ (j + 1)} =
        intervalColors (whichInterval e₁ j) by
          simp only [whichInterval, basePattern, intervalColors] at *; grind).ge
    · -- Boundary: last element of interval + first of next
      simp only [whichInterval] at hsame ⊢
      exact (show {basePattern e₁ j, basePattern e₁ (j + 1)} =
        intervalColors _ by grind [basePattern, intervalColors]).ge
  · -- Wrap: j = e₁ - 1
    push_neg at hj1
    have hj_eq : j = e₁ - 1 := by grind
    subst hj_eq
    have : e₁ - 1 + 1 = e₁ := by grind
    rw [this, Nat.mod_self]
    simp only [whichInterval] at *
    exact (show {basePattern e₁ (e₁ - 1), basePattern e₁ 0} =
      intervalColors _ by grind [basePattern, intervalColors]).ge

/-- A rotation by r ∈ [u, e₁-u] moves to a different interval:
    whichInterval(j) ≠ whichInterval((j + r) % e₁). -/
private lemma rotation_changes_interval {e₁ j : ℕ}
    (hge : e₁ ≥ 19) (hj : j < e₁)
    {r : ℕ} (hr_lo : case2d_u e₁ ≤ r) (hr_hi : r ≤ e₁ - case2d_u e₁) :
    whichInterval e₁ j ≠ whichInterval e₁ ((j + r) % e₁) := by
  have he₁_pos : 0 < e₁ := by grind
  have huv_bound := case2d_uv_le hge
  have hv_le_u : case2d_v e₁ ≤ case2d_u e₁ := by grind [case2d_u, case2d_v]
  have hw_le_u : e₁ - (case2d_u e₁ + case2d_v e₁) ≤ case2d_u e₁ := by grind [case2d_u, case2d_v]
  simp only [whichInterval]
  have hj'_lt : (j + r) % e₁ < e₁ := Nat.mod_lt _ he₁_pos
  intro heq
  by_cases hjr_wrap : j + r < e₁
  · -- No wrap
    rw [Nat.mod_eq_of_lt hjr_wrap] at heq hj'_lt
    grind
  · -- Wrap: (j + r) % e₁ = j + r - e₁
    push_neg at hjr_wrap
    have hmod : (j + r) % e₁ = j + r - e₁ := by
      have : r < e₁ := by grind
      have h1 : j + r - e₁ < e₁ := by grind
      rw [Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt this, if_neg (by grind)]
    grind

/-- Key polychromaticity lemma: if the base pattern is rotated by r ∈ [u, e₁-u],
    then at every position j, the 2×2 block covers all 3 colors. -/
private lemma basePattern_rotation_covers {e₁ j : ℕ} (he : Odd e₁) (hge : e₁ ≥ 19)
    {r : ℕ} (hr_lo : case2d_u e₁ ≤ r) (hr_hi : r ≤ e₁ - case2d_u e₁)
    (hj : j < e₁) :
    ∀ k : Fin 3, k ∈ ({basePattern e₁ j, basePattern e₁ ((j + 1) % e₁),
        basePattern e₁ ((j + r) % e₁),
        basePattern e₁ ((j + r + 1) % e₁)} : Finset (Fin 3)) := by
  intro k
  have he₁_pos : 0 < e₁ := by grind
  have hI := rotation_changes_interval hge hj hr_lo hr_hi
  have h1 := basePattern_consec_pair he hge hj
  have hjr : (j + r) % e₁ < e₁ := Nat.mod_lt _ he₁_pos
  have h2 := basePattern_consec_pair he hge hjr
  -- Rewrite ((j + r) % e₁ + 1) % e₁ = (j + r + 1) % e₁
  have hmod : ((j + r) % e₁ + 1) % e₁ = (j + r + 1) % e₁ := Nat.mod_add_mod (j + r) e₁ 1
  rw [hmod] at h2
  have hcov := intervalColors_union_covers hI k
  grind

private lemma case2d_wrap_shift {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (hd1_dvd : d₁ ∣ m)
    (hb_zero : (b : ZMod d₁) = 0)
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    (hord : addOrderOf (b : ZMod m) = e₁)
    (hm_eq : m = d₁ * e₁) :
    ∃ k₀ : ZMod e₁, (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  have hbij := orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
    set f := ZMod.castHom hd1_dvd (ZMod d₁)
    have hfφ : f (Φ q) = q.1 * ((b - a : ℤ) : ZMod d₁) := by
      change f (orbitMap m a b d₁ e₁ q) = _
      simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast, hb_zero, mul_zero, add_zero]
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
  have hq_eta : q = (q.1, q.2) := (Prod.eta q).symm
  rw [hq_eta] at hφq
  simp only [hq_i, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  grind

private lemma case2d_shift_ba_wrap {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero e₁] [NeZero d₁]
    (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁)
    (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (i : ZMod d₁) (hi : i.val = d₁ - 1) :
    ∀ (j : ZMod e₁),
      orbitMap m a b d₁ e₁ (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b d₁ e₁ (0, j + k₀) := by
  intro j
  simp only [orbitMap, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange i.val*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑i.val : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [hi, ← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑i.val : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j.val * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j.val * ((b : ℤ) : ZMod m) := by
    grind
  rw [step1]
  -- Step 2: d₁*(b-a) = k₀*b via hk₀
  rw [← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul]
  -- Step 3: k₀*b + j*b = (k₀+j)*b, reorder, convert to nsmul
  rw [← add_mul, ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Step 4: reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  have : (j + k₀).val = n % e₁ := by rw [ZMod.val_add]
  rw [this]
  have : n = e₁ * (n / e₁) + n % e₁ := (Nat.div_add_mod n e₁).symm
  conv_lhs => rw [this]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]

/-- Given d₁ ≥ 3 values each in [u, e₁-u] can sum to any target mod e₁,
    since the range has width ≥ e₁/3 and d₁ ≥ 3. -/
private lemma case2d_rotation_sum_exists {e₁ d₁ : ℕ} [NeZero d₁]
    (hd1_ge : d₁ ≥ 5) (he1_ge : e₁ ≥ 19) (he1_odd : Odd e₁)
    (target : ℕ) :
    ∃ vals : ZMod d₁ → ℕ,
      (∀ i, case2d_u e₁ ≤ vals i ∧ vals i ≤ e₁ - case2d_u e₁) ∧
      (Finset.univ.sum vals) % e₁ = target % e₁ := by
  have hu_lt : case2d_u e₁ < e₁ := by grind [case2d_u]
  have h2u : 2 * case2d_u e₁ < e₁ := by grind [case2d_u]
  have hdw' : d₁ * (e₁ - 2 * case2d_u e₁) ≥ e₁ := by
    change d₁ * (e₁ - 2 * (e₁ / 3 + e₁ % 3)) ≥ e₁
    obtain ⟨k, hk⟩ := he1_odd; subst hk
    have h5w : 5 * ((2 * k + 1) - 2 * ((2 * k + 1) / 3 + (2 * k + 1) % 3)) ≥ 2 * k + 1 := by grind
    exact le_trans h5w (by gcongr)
  set u := case2d_u e₁
  set w := e₁ - 2 * u
  have hw_pos : 0 < w := by grind
  have hdw : d₁ * w ≥ e₁ := hdw'
  set deficit := (target + e₁ * d₁ - d₁ * u) % e₁
  have hdef_lt : deficit < e₁ := Nat.mod_lt _ (by grind)
  set q := deficit / w
  set r := deficit % w
  have hr_lt : r < w := Nat.mod_lt _ hw_pos
  have hq_lt : q < d₁ := by
    by_contra! hge
    have h1 : deficit ≥ d₁ * w :=
      calc deficit ≥ deficit / w * w := Nat.div_mul_le_self deficit w
        _ = q * w := rfl
        _ ≥ d₁ * w := by gcongr
    grind
  have hqr : w * q + r = deficit := Nat.div_add_mod deficit w
  let f : ZMod d₁ → ℕ := fun i =>
    if i.val < q then e₁ - u else if i.val = q then u + r else u
  refine ⟨f, fun i => ?_, ?_⟩
  · grind
  · let g : ZMod d₁ → ℕ := fun i =>
      if i.val < q then w else if i.val = q then r else 0
    have hfg : ∀ i : ZMod d₁, f i = u + g i := by grind
    have hsum_f : Finset.univ.sum f = d₁ * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, ZMod.card]
    -- Helper: #{i : ZMod d₁ | p(i)} for decidable predicates on ZMod.val
    have hcard_lt : (Finset.univ.filter (fun i : ZMod d₁ => i.val < q)).card = q := by
      rw [← Finset.card_image_of_injective _ (ZMod.val_injective _),
        show Finset.image ZMod.val (Finset.univ.filter (fun i : ZMod d₁ => i.val < q)) =
          Finset.range q from by
            ext j; simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
            exact ⟨fun ⟨_, hx, he⟩ => he ▸ hx, fun hj => ⟨(j : ZMod d₁),
              by rwa [ZMod.val_natCast_of_lt (lt_trans hj hq_lt)],
              ZMod.val_natCast_of_lt (lt_trans hj hq_lt)⟩⟩,
        Finset.card_range]
    have hcard_eq : (Finset.univ.filter (fun i : ZMod d₁ => i.val = q)).card = 1 := by
      rw [show Finset.univ.filter (fun i : ZMod d₁ => i.val = q) = {(q : ZMod d₁)} from by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h => ZMod.val_injective _ (by rwa [ZMod.val_natCast_of_lt hq_lt]),
            fun h => by rw [h, ZMod.val_natCast_of_lt hq_lt]⟩,
        Finset.card_singleton]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have : ∀ i : ZMod d₁,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by grind
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        smul_eq_mul, hcard_lt, hcard_eq, one_mul]
    rw [hsum_f, hsum_g, Nat.mul_comm q w, hqr]
    simp only [deficit]
    rw [Nat.add_mod_mod]
    have hle : d₁ * u ≤ target + e₁ * d₁ :=
      le_add_left (le_trans (Nat.mul_le_mul_left d₁ (le_of_lt hu_lt)) (by rw [Nat.mul_comm]))
    have hadd : d₁ * u + (target + e₁ * d₁ - d₁ * u) = target + e₁ * d₁ := Nat.add_sub_cancel' hle
    rw [hadd, Nat.add_mul_mod_self_left]

private lemma zero_mem_zmod_set (m : ℕ) (a b : ℤ) : (0 : ZMod m) ∈ zmod_set m a b := by
  simp [zmod_set]

private lemma intCast_b_mem_zmod_set (m : ℕ) (a b : ℤ) : ((b : ℤ) : ZMod m) ∈ zmod_set m a b := by
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
    grind [ZMod.val_injective]
  grind

/-- When i is the max element, {k | k < i} ∪ {i} = univ. -/
private lemma zmod_filter_sum_last {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n)
    (hi : i.val = n - 1) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by
  rw [← zmod_filter_sum_succ f i]; congr 1; grind

-- Position arithmetic helpers for case2d_coloring_works (not important individually)

/-- Position shift by 1: adding 1 to ZMod coordinate shifts position by 1 mod n. -/
private lemma pos_shift_one {n : ℕ} [NeZero n] (j : ZMod n) (c : ℕ) :
    ((j + 1).val + c) % n = ((j.val + c) % n + 1) % n := by
  rw [ZMod.val_add_one, Nat.mod_add_mod, Nat.mod_add_mod]; grind

/-- (j + (S + V) % n) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_succ' (j S V n : ℕ) :
    (j + (S + V) % n) % n = ((j + S % n) % n + V) % n := by
  have h1 : j + (S + V) = j + S + V := by grind
  have h2 : (j + S) % n = (j + S % n) % n := (Nat.add_mod_mod j S n).symm
  rw [Nat.add_mod_mod, h1, ← Nat.mod_add_mod (j + S) n V, h2]

/-- Wrap case: if (S + V) % n = k₀ % n, then (j + k₀) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_wrap' (j S V k₀ n : ℕ)
    (hsum : (S + V) % n = k₀ % n) :
    (j + k₀) % n = ((j + S % n) % n + V) % n := by
  rw [← Nat.add_mod_mod j k₀ n, ← hsum, pos_shift_succ']

/-- **Subcase (2d) assembled.** Constructs the coloring for the case when both d₁
    and e₁ are odd with e₁ ≥ 19, using rotated interval patterns. -/
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
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd1_dvd).symm
  haveI : NeZero m := ⟨by grind⟩
  haveI : NeZero d₁ := ⟨by grind⟩
  haveI : NeZero e₁ := ⟨by grind⟩
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by grind) hd1_def
  have hb_zero : (b : ZMod d₁) = 0 := b_zero_mod_d1 hd1_def
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 hd1_dvd (by rwa [hd1_def]))
  have he1_b_zero : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  set Φ := Equiv.ofBijective _ (orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord)
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hd1_dvd hb_zero hba_unit hord hm_eq
  have hd1_ge5 : d₁ ≥ 5 := by grind
  obtain ⟨vals, hvals_bound, hvals_sum⟩ :=
    case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
  let rot : ZMod d₁ → ℕ := fun i =>
    ((Finset.univ.filter (fun j : ZMod d₁ => j.val < i.val)).sum vals) % e₁
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    basePattern e₁ ((coord.2.val + rot coord.1) % e₁)
  refine ⟨χ, fun n k => ?_⟩
  have hχ_eq : ∀ (i' : ZMod d₁) (j' : ZMod e₁),
      χ (Φ (i', j')) = basePattern e₁ ((j'.val + rot i') % e₁) := by
    intro i' j'; simp only [χ, Equiv.symm_apply_apply]
  set ij := Φ.symm n
  have hn : Φ ij = n := Equiv.apply_symm_apply Φ n
  set i := ij.1; set j := ij.2
  have hij : ij = (i, j) := (Prod.eta ij).symm
  set p := (j.val + rot i) % e₁ with hp_def
  have hp_lt : p < e₁ := Nat.mod_lt _ (NeZero.pos e₁)
  have hΦ_b : Φ (i, j + 1) = n + ((b : ℤ) : ZMod m) := by
    rw [← hn, hij]; exact (orbitMap_shift_b he1_b_zero (i, j)).symm
  have covers := basePattern_rotation_covers he1_odd he1_ge
    (hvals_bound i).1 (hvals_bound i).2 hp_lt k
  simp only [Finset.mem_insert, Finset.mem_singleton] at covers
  suffices ∃ (i_new : ZMod d₁) (j_new : ZMod e₁),
      Φ (i_new, j_new) = n + ((b - a : ℤ) : ZMod m) ∧
      (j_new.val + rot i_new) % e₁ = (p + vals i) % e₁ by
    obtain ⟨i_new, j_new, hΦ_ba, hpos⟩ := this
    have hΦ_2ba : Φ (i_new, j_new + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      rw [intCast_2ba_eq, ← add_assoc, ← hΦ_ba]
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
          = ((j_new.val + rot i_new) % e₁ + 1) % e₁ := pos_shift_one j_new (rot i_new)
        _ = ((p + vals i) % e₁ + 1) % e₁ := by rw [hpos]
        _ = (p + vals i + 1) % e₁ := Nat.mod_add_mod (p + vals i) e₁ 1
  by_cases hi : i.val + 1 < d₁
  · refine ⟨i + 1, j, ?_, ?_⟩
    · rw [← hn, hij]; exact (orbitMap_shift_ba i j hi).symm
    · change (j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < (i + 1).val)).sum vals) % e₁) % e₁ =
        ((j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
      have : (i + 1).val = i.val + 1 := by
        rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      rw [this, zmod_filter_sum_succ vals i]
      exact pos_shift_succ' j.val _ (vals i) e₁
  · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
    refine ⟨0, j + k₀, ?_, ?_⟩
    · rw [← hn, hij]
      exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    · have hrot0 : rot (0 : ZMod d₁) = 0 := by simp [rot, ZMod.val_zero]
      rw [hrot0, Nat.add_zero, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁
        (by rw [zmod_filter_sum_last vals i hi_eq, hvals_sum])

-- Mod 3 arithmetic: (a % e₁ + b) % 3 = (a + b) % 3 when 3 ∣ e₁
private lemma case2c_mod3 {e₁ : ℕ} (h3e : 3 ∣ e₁) (x y : ℕ) : (x % e₁ + y) % 3 = (x + y) % 3 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd x h3e, ← Nat.add_mod]

/-- **Subcase (2c):** d₁ and e₁ are both odd, with e₁ ≤ 17 and 3 ∣ e₁.
    Uses shifted periodic 012-patterns with different shifts for adjacent cycles. -/
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
  have hd1_gt1 : d₁ > 1 := by grind
  have he1_ge3 : e₁ ≥ 3 := by grind
  have hm_eq : m = d₁ * e₁ := (Nat.mul_div_cancel' hd1_dvd).symm
  haveI : NeZero m := ⟨by grind⟩
  haveI : NeZero d₁ := ⟨by grind⟩
  haveI : NeZero e₁ := ⟨by grind⟩
  have hord : addOrderOf (b : ZMod m) = e₁ := addOrderOf_b_eq (by grind) hd1_def
  have hb_zero : (b : ZMod d₁) = 0 := b_zero_mod_d1 hd1_def
  have hba_coprime := ba_coprime_d1 hd1_dvd (by rwa [hd1_def])
  have hba_unit := isUnit_intCast_of_natAbs_coprime hba_coprime
  have he1_b_zero : e₁ • (b : ZMod m) = 0 := hord ▸ addOrderOf_nsmul_eq_zero _
  have hbij := orbitMap_bijective hm_eq hd1_dvd hb_zero hba_unit hord
  set Φ := Equiv.ofBijective _ hbij
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hd1_dvd hb_zero hba_unit hord hm_eq
  have hd1_ge3 : d₁ ≥ 3 := by grind
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    ⟨(coord.2.val + (case2c_pattern d₁ k₀.val coord.1.val).val) % 3, Nat.mod_lt _ (by grind)⟩
  refine ⟨χ, fun n k => ?_⟩
  have hχ_eq : ∀ (i' : ZMod d₁) (j' : ZMod e₁),
      χ (Φ (i', j')) = ⟨(j'.val + (case2c_pattern d₁ k₀.val i'.val).val) % 3,
        Nat.mod_lt _ (by grind)⟩ := by
    intro i' j'; simp only [χ, Equiv.symm_apply_apply]
  set ij := Φ.symm n with hij_def
  have hn : Φ ij = n := Equiv.apply_symm_apply Φ n
  set i := ij.1 with hi_def
  set j := ij.2 with hj_def
  have hij : ij = (i, j) := (Prod.eta ij).symm
  set p := case2c_pattern d₁ k₀.val i.val
  have hzmod_succ : ∀ (jj : ZMod e₁),
      (jj + 1 : ZMod e₁).val = (jj.val + 1) % e₁ := ZMod.val_add_one
  have hΦ_b : Φ (i, j + 1) = n + ((b : ℤ) : ZMod m) := by
    rw [← hn, hij]; exact (orbitMap_shift_b he1_b_zero (i, j)).symm
  by_cases hi : i.val + 1 < d₁
  · set i' := i + 1
    set p' := case2c_pattern d₁ k₀.val i'.val
    have hΦ_ba : Φ (i', j) = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]; exact (orbitMap_shift_ba i j hi).symm
    have hΦ_2ba : Φ (i', j + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      rw [intCast_2ba_eq, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (i', j)).symm
    have hi'_eq : i'.val = i.val + 1 := by
      rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
    have hhyp : (j.val + p.val) % 3 ≠ (j.val + p'.val) % 3 := by
      change (j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3 ≠
        (j.val + (case2c_pattern d₁ k₀.val i'.val).val) % 3
      rw [hi'_eq]
      exact case2c_nonwrap_hyp d₁ k₀.val i.val j.val hd1_ge3 hd1_odd hi
    rcases cover_mod3_general p p' j.val j.val hhyp k with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b, by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · refine ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_b, hχ_eq, h]; congr 1; rw [hzmod_succ, case2c_mod3 he1_div3]
    · exact ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b,
        by rw [← hΦ_ba, hχ_eq, h]⟩
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1; rw [hzmod_succ, case2c_mod3 he1_div3]
  · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
    set j' : ZMod e₁ := j + k₀
    set p₀ := case2c_pattern d₁ k₀.val 0
    have hΦ_ba : Φ (0, j') = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]
      exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    have hΦ_2ba : Φ (0, j' + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      rw [intCast_2ba_eq, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (0, j')).symm
    have hp_eq : p = case2c_pattern d₁ k₀.val (d₁ - 1) := by grind
    have hhyp : (j.val + p.val) % 3 ≠ (j.val + k₀.val + p₀.val) % 3 := by
      rw [hp_eq]; exact case2c_wrap_hyp d₁ k₀.val j.val hd1_ge3 hd1_odd
    have hj'_val : j'.val = (j.val + k₀.val) % e₁ := ZMod.val_add j k₀
    rcases cover_mod3_general p p₀ j.val (j.val + k₀.val) hhyp k with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b, by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · refine ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_b, hχ_eq, h]; congr 1; rw [hzmod_succ, case2c_mod3 he1_div3]
    · refine ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_ba, hχ_eq, h]; congr 1
      change (j'.val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 = _
      rw [ZMod.val_zero, hj'_val]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) p₀.val
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      change ((j' + 1).val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 = _
      rw [ZMod.val_zero, hzmod_succ, hj'_val]
      rw [case2c_mod3 he1_div3, Nat.add_assoc, Nat.add_assoc]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) (1 + p₀.val)

/-- Auxiliary: rules out both cycle lengths being ≤ 17 when m ≥ 289. -/
private lemma no_both_e_small {m d₁ d₂ : ℕ}
    (hm : m ≥ 289) (hcop : Nat.gcd d₁ d₂ = 1)
    (hd₁_gt1 : d₁ > 1) (hd₂_gt1 : d₂ > 1)
    (hd₁_dvd : d₁ ∣ m) (hd₂_dvd : d₂ ∣ m)
    (he₁_le : m / d₁ ≤ 17) (he₂_le : m / d₂ ≤ 17) : False := by
  have hprod := Nat.le_of_dvd (by grind)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by rwa [Nat.Coprime]) hd₁_dvd hd₂_dvd)
  have h₁ : m ≤ d₁ * 17 := by rw [← Nat.mul_div_cancel' hd₁_dvd]; gcongr
  have h₂ : m ≤ d₂ * 17 := by rw [← Nat.mul_div_cancel' hd₂_dvd]; gcongr
  -- d₁*d₂ ≤ m ≤ d₁*17 → d₂ ≤ 17 → d₁ = d₂ = 17 → gcd = 17 ≠ 1
  have := Nat.le_of_mul_le_mul_left (hprod.trans h₁) (by grind)
  have := Nat.le_of_mul_le_mul_left (mul_comm d₁ d₂ ▸ hprod.trans h₂) (by grind)
  grind

/-! ### Aggregation of Case 2 -/

/-- **Main Case 2 (Multiple Cycles).** Aggregates all subcases (2a)–(2d).
    First applies WLOG to ensure 3 ∤ d₁, then dispatches on parity of d₁ and e₁. -/
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
            grind
          have hcop' : (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 := by
            grind
          have hmin' : min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 := by
            grind
          have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
            intro h3d'; have := Nat.dvd_gcd h3 h3d'
            grind
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
      have hd₂_pos : 0 < d₂ := Nat.pos_of_ne_zero (by grind)
      by_cases he_le : e₁ ≤ 17
      · -- Case 2c: prove 3 ∣ e₁
        -- Since gcd(d₁,d₂)=1 and 3 ∤ d₁, if 3 ∣ d₂ then 3 ∣ m hence 3 ∣ e₁.
        -- If 3 ∤ d₂: swap and show e₂ ≥ 19 (contradiction with both ≤ 17).
        by_cases h3d₂ : 3 ∣ d₂
        · have h3m : 3 ∣ m := dvd_trans h3d₂ hd₂_dvd
          have h3e₁ : 3 ∣ e₁ := by
            have h3de : 3 ∣ d₁ * e₁ := Nat.mul_div_cancel' hd₁_dvd ▸ h3m
            have hcop3 : Nat.Coprime 3 d₁ := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3_nd₁
            exact hcop3.dvd_of_dvd_mul_left h3de
          exact case_two_odd_small m a' b' hm hcop hmin hd₁_odd he₁_odd he_le h3e₁
        · -- 3 ∤ d₁ and 3 ∤ d₂ and e₁ ≤ 17: swap and show new e₁ ≥ 19.
          -- After swap, new e₁' = m/d₂. If e₁' ≤ 17 too, contradiction.
          rw [← zmod_set_swap m a' b']
          set a'' := (-a' : ℤ); set b'' := (b' - a' : ℤ)
          have hba_eq : (b'' - a'').natAbs = b'.natAbs := by
            grind
          have hcop' : (Nat.gcd b''.natAbs m).gcd (Nat.gcd (b'' - a'').natAbs m) = 1 := by
            grind
          have hmin' : min (Nat.gcd b''.natAbs m) (Nat.gcd (b'' - a'').natAbs m) > 1 := by
            grind
          -- Dispatch on parity
          rcases Nat.even_or_odd (m / Nat.gcd b''.natAbs m) with he' | ho'
          · exact case_two_e1_even m a'' b'' hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b''.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd m a'' b'' hm hcop' hmin' hd' ho'
            · -- Both odd after swap. Show e₁' ≥ 19 by contradiction.
              have he₁'_ge : m / Nat.gcd b''.natAbs m ≥ 19 := by
                by_contra hlt; push_neg at hlt
                rw [Nat.gcd_comm] at hcop
                exact no_both_e_small hm hcop (by grind) (by grind) hd₂_dvd hd₁_dvd (by grind) he_le
              exact case2d_coloring_works hm hcop' hmin' hd' ho' he₁'_ge h3d₂
      · have he₁_ge : e₁ ≥ 19 := by grind
        exact case2d_coloring_works hm hcop hmin hd₁_odd he₁_odd he₁_ge h3_nd₁

end Case2_MultipleCycles
