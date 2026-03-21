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

variable {m : ℕ} {a b : ℤ}

local notation "d₁" => Nat.gcd b.natAbs m
local notation "d₂" => Nat.gcd (Int.natAbs (b - a)) m
local notation "e₁" => m / d₁

/-! ### Arithmetic helpers for cycle decomposition

These lemmas set up the orbit map infrastructure. They are not important individually
but are used throughout Case 2.
-/

private lemma intCast_2ba_eq :
    ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by grind

private lemma ZMod.val_add_one {n : ℕ} [NeZero n] (x : ZMod n) : (x + 1).val = (x.val + 1) % n := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]

private lemma zmod_val_add_one (d : ℕ) [NeZero d] (i : ZMod d) :
    (i + 1).val = if i.val + 1 < d then i.val + 1 else 0 := by
  rw [ZMod.val_add_one]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · grind [Nat.mod_self]

private lemma parity_flip_even (e : ℕ) [NeZero e] (he : Even e)
    (j : ZMod e) : j.val % 2 ≠ (j + 1).val % 2 := by grind [zmod_val_add_one e j]

/--
A coloring for Case 2a ($e_1$ even).
Each cycle $i$ uses two colors that alternate based on position parity.
Cycles are assigned "missing colors" such that no two adjacent cycles miss the same color.
-/
private def cycle_coloring (d e : ℕ) : ZMod d × ZMod e → Fin 3 := fun ⟨i, j⟩ =>
  if i.val = d - 1 ∧ ¬Even d then ⟨1 + j.val % 2, by grind⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by grind⟩
  else ⟨2 * (j.val % 2), by grind⟩

-- Coverage: adjacent cycles cover all 3 colors.
private lemma color_covers_even (d e : ℕ) [NeZero d] [NeZero e] (hd_ge2 : d ≥ 2)
    (hparity : ∀ j : ZMod e, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d) (j₁ j₂ : ZMod e) (k : Fin 3) :
    k = cycle_coloring d e (i, j₁) ∨
    k = cycle_coloring d e (i, j₁ + 1) ∨
    k = cycle_coloring d e (i + 1, j₂) ∨
    k = cycle_coloring d e (i + 1, j₂ + 1) := by
  grind [cycle_coloring, Fin.ext_iff, zmod_val_add_one]

private lemma d₁_dvd_m : d₁ ∣ m := Nat.gcd_dvd_right _ _
private lemma m_eq_d₁_mul_e₁ : m = d₁ * e₁ := (Nat.mul_div_cancel' (d₁_dvd_m (b := b))).symm

instance neZero_d₁ [NeZero m] : NeZero d₁ :=
  ⟨fun h => absurd (by rw [m_eq_d₁_mul_e₁ (m := m) (b := b), h, zero_mul]) (NeZero.ne m)⟩

instance neZero_e₁ [NeZero m] : NeZero e₁ :=
  ⟨fun h => absurd (by rw [m_eq_d₁_mul_e₁ (m := m) (b := b), h, mul_zero]) (NeZero.ne m)⟩

/-! ### Orbit coloring framework -/

section OrbitFramework

/--
The orbit map $\phi : \mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \to \mathbb{Z}_m$ defined by
$\phi(i, j) = i(b-a) + jb \pmod m$. This map is a bijection when $\gcd(b-a, b, m) = 1$.
It provides the coordinate system used to analyze the "Multiple Cycles" case.
-/
private def orbitMap (m : ℕ) (a b : ℤ) : ZMod d₁ × ZMod e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b

private lemma addOrderOf_b_eq [NeZero m] : addOrderOf (b : ZMod m) = e₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = e₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (NeZero.ne m), Nat.gcd_comm]
  rcases Int.natAbs_eq b with h | h
  · have : (b : ZMod m) = (b.natAbs : ZMod m) := by rw [h]; simp
    grind
  · have : (b : ZMod m) = -(b.natAbs : ZMod m) := by rw [h]; simp
    rw [this, addOrderOf_neg]
    exact key

private lemma d₁_dvd_b : (d₁ : ℤ) ∣ b :=
  Int.natCast_dvd.mpr (Nat.gcd_dvd_left b.natAbs m)

private lemma b_zero_mod_d1 [NeZero m] : (b : ZMod d₁) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (d₁_dvd_b (b := b))

private lemma ba_coprime_d1 (h_gcd_coprime : Nat.gcd d₁ d₂ = 1) :
    Nat.Coprime (b - a).natAbs d₁ :=
  Nat.dvd_one.mp (h_gcd_coprime ▸ Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      (Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (dvd_trans (Nat.gcd_dvd_right _ _) d₁_dvd_m)))

private lemma orbitMap_i_eq [NeZero m] (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁))
    {i₁ i₂ : ZMod d₁} {j₁ j₂ : ZMod e₁}
    (heq : orbitMap m a b (i₁, j₁) = orbitMap m a b (i₂, j₂)) : i₁ = i₂ := by
  simp only [orbitMap] at heq
  have := congr_arg (ZMod.castHom d₁_dvd_m (ZMod d₁)) heq
  simp only [map_add, map_mul, map_natCast, map_intCast] at this
  simp only [b_zero_mod_d1, mul_zero, add_zero, ZMod.natCast_val, ZMod.cast_id] at this
  exact hba_unit.mul_right_cancel this

private lemma orbitMap_j_eq [NeZero m] {j₁ j₂ : ZMod e₁}
    (hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m)) : j₁ = j₂ := by
  wlog h : j₁.val ≤ j₂.val with H
  · exact (H hj_smul.symm (Nat.le_of_not_le h)).symm
  · have h3 : (j₂.val - j₁.val) • (b : ZMod m) = 0 :=
      add_left_cancel (a := j₁.val • (b : ZMod m))
        (by rw [add_zero, ← add_nsmul, Nat.add_sub_cancel' h]; exact hj_smul.symm)
    have := Nat.eq_zero_of_dvd_of_lt
      ((addOrderOf_b_eq (b := b) (m := m)) ▸ addOrderOf_dvd_of_nsmul_eq_zero h3)
      (by grind [ZMod.val_lt j₁, ZMod.val_lt j₂])
    exact ZMod.val_injective _ (by grind)

private lemma orbitMap_injective [NeZero m] (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)) :
    Function.Injective (orbitMap m a b : ZMod d₁ × ZMod e₁ → ZMod m) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ heq
  have hi := orbitMap_i_eq hba_unit heq
  subst hi
  simp only [orbitMap] at heq
  have hj_smul : (j₁.val : ℕ) • (b : ZMod m) = (j₂.val : ℕ) • (b : ZMod m) := by grind
  exact Prod.ext rfl (orbitMap_j_eq hj_smul)

private lemma orbitMap_bijective [NeZero m] (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)) :
    Function.Bijective (orbitMap m a b : ZMod d₁ × ZMod e₁ → ZMod m) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨orbitMap_injective hba_unit,
     by simp only [Fintype.card_prod, ZMod.card]; linarith [hm_eq]⟩

private lemma orbitMap_shift_b [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0) :
    ∀ p : ZMod d₁ × ZMod e₁, orbitMap m a b p + (b : ZMod m) = orbitMap m a b (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]
    grind
  · have hje : j.val + 1 = e₁ := by grind [ZMod.val_lt]
    have hv : (j + 1).val = 0 := by rw [ZMod.val_add_one, hje, Nat.mod_self]
    have h1 : (j.val : ZMod m) * ↑b + ↑b = 0 := by
      have : (j.val : ZMod m) * ↑b + ↑b = (j.val + 1 : ℕ) • (b : ZMod m) := by
        rw [add_nsmul, one_nsmul, nsmul_eq_mul]
      rw [this, hje, he1_b_zero]
    rw [hv, Nat.cast_zero, zero_mul, add_zero, add_assoc, h1, add_zero]

private lemma orbitMap_shift_ba [NeZero m] (i : ZMod d₁) (j : ZMod e₁) (hi : i.val + 1 < d₁) :
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b (i + 1, j) := by
  simp only [orbitMap]
  have : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
  rw [this]
  grind

/-- The cycle index α(x) = castHom(x) * u⁻¹ satisfies α(φ(i,j)) = i. -/
private lemma orbitMap_cycle_index [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (i : ZMod d₁) (j : ZMod e₁) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (orbitMap m a b (i, j)) * u⁻¹ = i := by
  simp only [orbitMap]
  rw [map_add, map_mul, map_mul, map_natCast, map_intCast, map_natCast, map_intCast,
    b_zero_mod_d1, mul_zero, add_zero, mul_assoc, ← hu, u.mul_inv, mul_one]
  simp [ZMod.natCast_val]

/-- The cycle index α shifts by 1 when (b-a) is added. -/
private lemma cycle_index_shift_ba [NeZero m]
    (u : (ZMod d₁)ˣ) (hu : ↑u = ((b - a : ℤ) : ZMod d₁)) (x : ZMod m) :
    ZMod.castHom d₁_dvd_m (ZMod d₁) (x + ↑(b - a)) * u⁻¹ =
    ZMod.castHom d₁_dvd_m (ZMod d₁) x * u⁻¹ + 1 := by
  simp only [map_add, map_intCast, add_mul]
  rw [← hu]
  ring_nf
  rw [u.inv_mul]
  ring

/-- If Φ(i, j+1) = Φ(i, j) + b, then Φ⁻¹(x+b) = (same_i, j+1). -/
private lemma equiv_symm_shift_b {γ : Type*} [AddCommMonoid γ]
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) {b : γ}
    (hΦ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, Φ (i, j + 1) = Φ (i, j) + b) (x : γ) :
    Φ.symm (x + b) = ((Φ.symm x).1, (Φ.symm x).2 + 1) := by grind

/-- If α(Φ(i,j)) = i for all i,j, then (Φ⁻¹(x)).1 = α(x). -/
private lemma equiv_symm_fst_eq {γ : Type*} (Φ : ZMod d₁ × ZMod e₁ ≃ γ) (α : γ → ZMod d₁)
    (hα : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (Φ (i, j)) = i) (x : γ) :
    (Φ.symm x).1 = α x := by grind

/-- Build the orbit equivalence from the standard hypotheses. -/
private noncomputable def orbitEquiv [NeZero m]
    (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)) : ZMod d₁ × ZMod e₁ ≃ ZMod m :=
  Equiv.ofBijective (orbitMap m a b) (orbitMap_bijective hba_unit)

private lemma orbitEquiv_shift_b [NeZero m] {hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)}
    (x : ZMod m) :
    (orbitEquiv hba_unit).symm (x + ↑b) =
    (((orbitEquiv hba_unit).symm x).1, ((orbitEquiv hba_unit).symm x).2 + 1) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  exact equiv_symm_shift_b _ (fun i j =>
    (orbitMap_shift_b (addOrderOf_b_eq (b := b) (m := m) ▸
      addOrderOf_nsmul_eq_zero _) (i, j)).symm) x

private lemma orbitEquiv_cycle_shift [NeZero m] {hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)}
    (x : ZMod m) :
    ((orbitEquiv hba_unit).symm (x + ↑(b - a))).1 = ((orbitEquiv hba_unit).symm x).1 + 1 := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  let u_ba := hba_unit.choose
  have hu_ba : ↑u_ba = ((b - a : ℤ) : ZMod d₁) := hba_unit.choose_spec
  let α : ZMod m → ZMod d₁ := fun x => ZMod.castHom d₁_dvd_m (ZMod d₁) x * u_ba⁻¹
  have hΦ_cycle := equiv_symm_fst_eq (orbitEquiv hba_unit) α
    (orbitMap_cycle_index u_ba hu_ba)
  rw [hΦ_cycle (x + ↑(b - a))]
  dsimp only [α]
  rw [cycle_index_shift_ba u_ba hu_ba]
  congr 1
  exact (hΦ_cycle x).symm

/-- In the non-wrap case, the second coordinate is preserved by the (b-a) shift. -/
private lemma orbitEquiv_snd_shift_ba [NeZero m] {hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)}
    (n : ZMod m) (hi : (orbitEquiv hba_unit).symm n |>.1.val + 1 < d₁) :
    ((orbitEquiv hba_unit).symm (n + ↑(b - a))).2 = ((orbitEquiv hba_unit).symm n).2 := by
  set Φ := orbitEquiv hba_unit
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := orbitMap_shift_ba (a := a) i j hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ (i + 1, j) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    rw [← hn]
    exact hshift.symm
  have h : Φ.symm (n + ↑(b - a)) = (i + 1, j) := by rw [← hΦ, Φ.symm_apply_apply]
  rw [h]

/-- **Key infrastructure for Case 2.** Polychromaticity from an orbit coloring:
    given an orbit equivalence Φ with shift properties and a coloring f,
    if f covers all colors at any translate, then f ∘ Φ.symm is polychromatic.
    All four Case 2 subcases use this as their final step. -/
private lemma orbit_coloring_polychrom (Φ : ZMod d₁ × ZMod e₁ ≃ ZMod m)
    (hΦ_add_b : ∀ x : ZMod m, Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1))
    (hΦ_cycle_shift : ∀ x : ZMod m, (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1)
    (f : ZMod d₁ × ZMod e₁ → Fin 3) (hcovers : ∀ (n : ZMod m) (k : Fin 3),
      k = f ((Φ.symm n).1, (Φ.symm n).2) ∨
      k = f ((Φ.symm n).1, (Φ.symm n).2 + 1) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2) ∨
      k = f ((Φ.symm n).1 + 1, (Φ.symm (n + ↑(b - a))).2 + 1)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  let χ : ZMod m → Fin 3 := f ∘ Φ.symm
  refine ⟨χ, fun n k => ?_⟩
  simp only [zmod_set, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  set j' := (Φ.symm (n + ↑(b - a))).2
  have hχ_n : χ n = f (i, j) := rfl
  have hχ_nb : χ (n + ↑b) = f (i, j + 1) := congr_arg f (hΦ_add_b n)
  have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') := congr_arg f (Prod.ext (hΦ_cycle_shift n) rfl)
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
lemma case_two_e1_even (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (he1_even : Even e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  haveI : NeZero m := ⟨by grind⟩
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  exact orbit_coloring_polychrom (orbitEquiv hba_unit) orbitEquiv_shift_b
    orbitEquiv_cycle_shift (cycle_coloring d₁ e₁)
    (fun n k => color_covers_even d₁ e₁ (by grind) (parity_flip_even e₁ he1_even) _ _ _ k)

/-! ### Subcase (2b) construction: d₁ even, e₁ odd

The coloring assigns each even cycle the pattern `01010…011` and each odd cycle
the pattern `22020…020`. The degenerate pairs `{1,1}` and `{2,2}` occur at
positions `j = e₁ − 2` and `j = 0` respectively; since `e₁ ≥ 3` these positions
are distinct, guaranteeing every 2×2 block contains all three colors.
-/

-- The coloring function for Case 2b.
-- Even cycles: 01010...011 (alternating 0,1, last position overridden to 1)
-- Odd cycles: 22020...020 (first position 2, then: even→0, odd→2)
private def case2b_coloring (d e : ℕ) : ZMod d × ZMod e → Fin 3 := fun ⟨i, j⟩ =>
  if i.val % 2 = 0 -- even cycle
  then if j.val = e - 1 then 1 else if j.val % 2 = 0 then 0 else 1
  else if j.val = 0 then 2 else if j.val % 2 = 0 then 0 else 2 -- odd cycle

-- Coverage — any 2×2 block covers all 3 colors.
-- The compatibility says degenerate positions can't coincide:
-- odd-degenerate at j=0 and even-degenerate at j=e₁-2 are incompatible.
private lemma case2b_coverage_gen (d e : ℕ) [NeZero d] [NeZero e] (hd_even : Even d)
    (he_odd : Odd e) (he_ge3 : e ≥ 3) (i : ZMod d) (j₁ j₂ : ZMod e)
    (h_compat : j₁.val = 0 → j₂.val ≠ e - 2)
    (h_compat' : j₂.val = 0 → j₁.val ≠ e - 2) (k : Fin 3) :
    k = case2b_coloring d e (i, j₁) ∨
    k = case2b_coloring d e (i, j₁ + 1) ∨
    k = case2b_coloring d e (i + 1, j₂) ∨
    k = case2b_coloring d e (i + 1, j₂ + 1) := by
  grind [case2b_coloring, zmod_val_add_one e j₁, zmod_val_add_one e j₂,
    parity_flip_even d hd_even i]

/-! ### Subcase (2b) main lemma -/

/-- **Subcase (2b).** $d_1$ is even and $e_1$ is odd.
    Alternating patterns with a "degenerate" position fixup at different positions
    for even and odd cycles, ensuring they do not overlap across adjacent cycles. -/
lemma case_two_d1_even_e1_odd (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (hd1_even : Even d₁) (he1_odd : Odd e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  -- e₁ ≥ 3: e₁ is odd and e₁ = 1 would give d₁ = m, contradicting gcd(d₁,d₂) = 1
  have he₁_ge3 : e₁ ≥ 3 := by
    by_contra! h
    rcases (by grind : e₁ = 1 ∨ e₁ = 2) with he | he
    · have : d₂ ∣ d₁ := by
        have : m = d₁ := by have := hm_eq; rw [he, mul_one] at this; exact this
        rw [← this]
        exact Nat.gcd_dvd_right _ _
      exact absurd (Nat.eq_one_of_dvd_one
        (h_gcd_coprime ▸ Nat.dvd_gcd this (dvd_refl _))) (by grind)
    · grind
  haveI : NeZero m := ⟨by grind⟩
  have hba_unit : IsUnit (Int.cast (b - a) : ZMod d₁) :=
    isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  let Φ := orbitEquiv hba_unit
  -- d₂ properties for the compatibility argument
  have hd₂_dvd : d₂ ∣ m := Nat.gcd_dvd_right _ _
  have hd₂_gt1 : d₂ > 1 := by grind
  have hd₂_dvd_ba : (d₂ : ℤ) ∣ (b - a) := by simpa [Int.gcd] using Int.gcd_dvd_left (b - a) (m : ℤ)
  have hd₂_dvd_e₁ : d₂ ∣ e₁ := by
    exact (by rwa [Nat.Coprime, Nat.gcd_comm] : Nat.Coprime d₂ d₁).dvd_of_dvd_mul_right
      (mul_comm d₁ e₁ ▸ hm_eq ▸ hd₂_dvd)
  -- Projection: π(φ(i,j)) = j.val * π(b) since π(b-a) = 0
  haveI : NeZero d₂ := ⟨by grind⟩
  let π : ZMod m → ZMod d₂ := ZMod.castHom hd₂_dvd (ZMod d₂)
  have hπ_Φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, π (Φ (i, j)) = (j.val : ZMod d₂) * π (↑b) := by
    intro i j
    change π (orbitMap m a b (i, j)) = _
    simp only [orbitMap, π, map_add, map_mul, map_natCast, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba]
    ring
  -- π(b) is a unit in ZMod d₂
  have hπ_b_unit : IsUnit (π (↑b)) := by
    simp only [π, map_intCast]
    exact isUnit_intCast_of_natAbs_coprime (by grind)
  -- Degenerate positions can't coincide: use d₂ | (j-j') from projection
  -- π(n+(b-a)) = π(n) since π(b-a)=0, combined with π(φ(i,j))=j.val*π(b)
  -- gives d₂ | (j.val - j'.val). Then d₂ | e₁ and d₂ > 1, so e₁-2 and 0
  -- can't both be divisible by d₂ (since e₁ odd → gcd(e₁-2, e₁) | 2).
  have h_degenerate_false : ∀ (j₁ j₂ : ZMod e₁),
      (j₁.val : ZMod d₂) * π (↑b) = (j₂.val : ZMod d₂) * π (↑b) →
      j₁.val = 0 → j₂.val = e₁ - 2 → False := by
    intro j₁ j₂ heq hj₁ hj₂
    have hval_eq := hπ_b_unit.mul_right_cancel heq
    rw [hj₁, hj₂, Nat.cast_zero] at hval_eq
    have hd₂_dvd_diff := (ZMod.natCast_eq_zero_iff _ _).mp hval_eq.symm
    have hd₂_dvd_2 : d₂ ∣ 2 := by
      have h := Nat.dvd_sub hd₂_dvd_e₁ hd₂_dvd_diff
      have : e₁ - (e₁ - 2) = 2 := by grind
      rwa [this] at h
    obtain ⟨_, hk⟩ := hd₂_dvd_e₁
    obtain ⟨_, hl⟩ := he1_odd
    have := Nat.le_of_dvd (by grind) hd₂_dvd_2
    grind
  -- π(n) and π(n+(b-a)) give the same ZMod d₂ value
  have hπ_eq : ∀ n : ZMod m, π (n + ↑(b - a)) = π n := fun n => by
    simp only [π, map_add, map_intCast]
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd₂_dvd_ba, add_zero]
  exact orbit_coloring_polychrom Φ orbitEquiv_shift_b orbitEquiv_cycle_shift
    (case2b_coloring d₁ e₁) (fun n k => by
      set p := Φ.symm n
      set j := p.2
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
private def case2c_pattern (d k₀ i : ℕ) : Fin 3 :=
  if i = d - 1 ∧ d % 2 = 1 then if k₀ % 3 = 2 then 1 else 2
  else if i % 2 = 0 then 0
  else if k₀ % 3 = 2 then 2 else 1

-- General coverage: if (j₁ + p₁) % 3 ≠ (j₂ + p₂) % 3, all 3 colors appear.
private lemma cover_mod3_general (p₁ p₂ : Fin 3) (j₁ j₂ : ℕ)
    (hne : (j₁ + p₁.val) % 3 ≠ (j₂ + p₂.val) % 3) (k : Fin 3) :
    k = ⟨(j₁ + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₁ + 1 + p₁.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ ∨
    k = ⟨(j₂ + 1 + p₂.val) % 3, Nat.mod_lt _ (by grind)⟩ := by
  by_contra! hall
  obtain ⟨h1, h2, h3, h4⟩ := hall
  grind [Fin.ext_iff]

-- Non-wrap coverage hypothesis: j₁ = j₂, patterns differ → hypothesis holds.
private lemma case2c_nonwrap_hyp (d k₀ i j : ℕ) (hd : d ≥ 3)
    (hd_odd : Odd d) (hi : i + 1 < d) : (j + (case2c_pattern d k₀ i).val) % 3 ≠
    (j + (case2c_pattern d k₀ (i + 1)).val) % 3 := by
  obtain ⟨k, hk⟩ := hd_odd
  subst hk
  grind [case2c_pattern]

-- Wrap coverage hypothesis: j₂ = j₁ + k₀, pattern chosen to avoid conflict.
private lemma case2c_wrap_hyp (d k₀ j : ℕ) (hd : d ≥ 3) (hd_odd : Odd d) :
    (j + (case2c_pattern d k₀ (d - 1)).val) % 3 ≠
    (j + k₀ + (case2c_pattern d k₀ 0).val) % 3 := by
  obtain ⟨k, hk⟩ := hd_odd
  subst hk
  grind [case2c_pattern]

/-! ### Subcase (2d): d₁, e₁ both odd, e₁ ≥ 19

The most technically involved subcase. The base pattern on C₀ uses three
alternating bicolor intervals of sizes u, v, w. Each subsequent cycle is a
rotation of C₀. The many private lemmas below are technical helpers for
verifying the rotation property; the important result is `case2d_coloring_works`.
-/

/-- Partition parameter: first interval size for case 2d.
    u = e₁/3 + e₁%3 (i.e. k+r where e₁ = 3k+r).
    For e₁ odd: r=0 → u=k (odd), r=1 → u=k+1 (odd), r=2 → u=k+2 (odd). -/
private def case2d_u (e : ℕ) : ℕ := e / 3 + e % 3

/-- Second interval size for case 2d.
    v = e₁/3 + (1 if e₁%3 = 1 else 0).
    r=0: v = k   r=1: v = k+1   r=2: v = k -/
private def case2d_v (e : ℕ) : ℕ := if e % 3 = 1 then e / 3 + 1 else e / 3

private lemma case2d_uv_le {e : ℕ} (hge : e ≥ 19) : case2d_u e + case2d_v e ≤ e := by
  grind [case2d_u, case2d_v]

/-- The base pattern: three alternating bicolor intervals on {0,...,e₁-1}.
    Positions 0..u-1: alternating 0,1 (starts and ends with 0 since u is odd)
    Positions u..u+v-1: alternating 1,2 (starts and ends with 1)
    Positions u+v..e₁-1: alternating 2,0 (starts and ends with 2) -/
private def basePattern (e : ℕ) (j : ℕ) : Fin 3 := let u := case2d_u e
  let v := case2d_v e
  if j < u then if j % 2 = 0 then 0 else 1
  else if j < u + v then if (j - u) % 2 = 0 then 1 else 2
  else if (j - u - v) % 2 = 0 then 2 else 0

/-- Which interval (0, 1, or 2) a position j falls in. -/
private def whichInterval (e j : ℕ) : Fin 3 := let u := case2d_u e
  let v := case2d_v e
  if j < u then 0 else if j < u + v then 1 else 2

/-- The color pair for each interval. -/
private def intervalColors : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

/-- Combined: for any j, {basePattern(j), basePattern(j+1 mod e₁)} is the
    interval pair of whichInterval(j). -/
private lemma basePattern_consec_pair {e j : ℕ} (he : Odd e) (hge : e ≥ 19) (hj : j < e) :
    intervalColors (whichInterval e j) ⊆ {basePattern e j, basePattern e ((j + 1) % e)} := by
  obtain ⟨ku, hku⟩ : Odd (case2d_u e) := by obtain ⟨k, hk⟩ := he; grind [case2d_u]
  obtain ⟨kv, hkv⟩ : Odd (case2d_v e) := by obtain ⟨k, hk⟩ := he; grind [case2d_v]
  obtain ⟨kw, hkw⟩ : Odd (e - case2d_u e - case2d_v e) := by
    obtain ⟨k, hk⟩ := he; grind [case2d_u, case2d_v]
  have huv := case2d_uv_le hge
  by_cases hj1 : j + 1 < e
  · rw [Nat.mod_eq_of_lt hj1]
    by_cases hsame : whichInterval e j = whichInterval e (j + 1)
    · -- Same interval: both colors present
      have : {basePattern e j, basePattern e (j + 1)} = intervalColors (whichInterval e j) := by
        simp only [whichInterval, basePattern, intervalColors] at *
        grind
      exact this.ge
    · -- Boundary: last element of interval + first of next
      have : intervalColors (whichInterval e j) ⊆ {basePattern e j, basePattern e (j + 1)} := by
        simp only [whichInterval] at hsame ⊢
        grind [basePattern, intervalColors]
      exact this
  · -- Wrap: j = e - 1
    push_neg at hj1
    have hj_eq : j = e - 1 := by grind
    subst hj_eq
    have : e - 1 + 1 = e := by grind
    rw [this, Nat.mod_self]
    have : intervalColors (whichInterval e (e - 1)) ⊆
        {basePattern e (e - 1), basePattern e 0} := by
      simp only [whichInterval]
      grind [basePattern, intervalColors]
    exact this

/-- A rotation by r ∈ [u, e₁-u] moves to a different interval:
    whichInterval(j) ≠ whichInterval((j + r) % e₁). -/
private lemma rotation_changes_interval {e j : ℕ} (hge : e ≥ 19) (hj : j < e)
    {r : ℕ} (hr_lo : case2d_u e ≤ r) (hr_hi : r ≤ e - case2d_u e) :
    whichInterval e j ≠ whichInterval e ((j + r) % e) := by
  have he_pos : 0 < e := by grind
  have huv_bound := case2d_uv_le hge
  have hv_le_u : case2d_v e ≤ case2d_u e := by grind [case2d_u, case2d_v]
  have hw_le_u : e - (case2d_u e + case2d_v e) ≤ case2d_u e := by grind [case2d_u, case2d_v]
  simp only [whichInterval]
  have hj'_lt : (j + r) % e < e := Nat.mod_lt _ he_pos
  intro heq
  by_cases hjr_wrap : j + r < e
  · -- No wrap
    rw [Nat.mod_eq_of_lt hjr_wrap] at heq hj'_lt
    grind
  · -- Wrap: (j + r) % e = j + r - e
    push_neg at hjr_wrap
    have hmod : (j + r) % e = j + r - e := by
      have : r < e := by grind
      have h1 : j + r - e < e := by grind
      rw [Nat.add_mod_eq_sub, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt this, if_neg (by grind)]
    grind

/-- Key polychromaticity lemma: if the base pattern is rotated by r ∈ [u, e₁-u],
    then at every position j, the 2×2 block covers all 3 colors. -/
private lemma basePattern_rotation_covers {e j : ℕ} (he : Odd e) (hge : e ≥ 19)
    {r : ℕ} (hr_lo : case2d_u e ≤ r) (hr_hi : r ≤ e - case2d_u e) (hj : j < e) :
    ∀ k : Fin 3, k ∈ ({basePattern e j, basePattern e ((j + 1) % e),
        basePattern e ((j + r) % e), basePattern e ((j + r + 1) % e)} : Finset (Fin 3)) := by
  intro k
  have he_pos : 0 < e := by grind
  have hI := rotation_changes_interval hge hj hr_lo hr_hi
  have h1 := basePattern_consec_pair he hge hj
  have hjr : (j + r) % e < e := Nat.mod_lt _ he_pos
  have h2 := basePattern_consec_pair he hge hjr
  -- Rewrite ((j + r) % e + 1) % e = (j + r + 1) % e
  have hmod : ((j + r) % e + 1) % e = (j + r + 1) % e := Nat.mod_add_mod (j + r) e 1
  rw [hmod] at h2
  have : ∀ (i₁ i₂ : Fin 3), i₁ ≠ i₂ → k ∈ intervalColors i₁ ∨ k ∈ intervalColors i₂ := by
    intro i₁ i₂; fin_cases i₁ <;> fin_cases i₂ <;> fin_cases k <;>
      simp_all [intervalColors, Finset.mem_insert, Finset.mem_singleton]
  grind

private lemma case2d_wrap_shift [NeZero m] (hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)) :
    ∃ k₀ : ZMod e₁, (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m) := by
  set Φ := orbitEquiv hba_unit
  set q := Φ.symm ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  have hq_i : q.1 = 0 := by
    set f := ZMod.castHom d₁_dvd_m (ZMod d₁)
    have hfφ : f (Φ q) = q.1 * ((b - a : ℤ) : ZMod d₁) := by
      change f (orbitMap m a b q) = _
      simp only [orbitMap, map_add, map_mul, map_natCast, map_intCast,
        b_zero_mod_d1, mul_zero, add_zero]
      rw [ZMod.natCast_val, ZMod.cast_id]
    rw [Equiv.apply_symm_apply] at hfφ
    have : f (d₁ • ((b - a : ℤ) : ZMod m)) = 0 := by
      rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
    rw [this] at hfφ
    exact hba_unit.mul_left_eq_zero.mp hfφ.symm
  refine ⟨q.2, ?_⟩
  have hφq := Equiv.apply_symm_apply Φ ((d₁ : ℕ) • ((b - a : ℤ) : ZMod m))
  change orbitMap m a b q = _ at hφq
  simp only [orbitMap] at hφq
  rw [(Prod.eta q).symm] at hφq
  simp only [hq_i, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add] at hφq
  grind

private lemma case2d_shift_ba_wrap [NeZero m] (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (i : ZMod d₁) (hi : i.val = d₁ - 1) : ∀ (j : ZMod e₁),
    orbitMap m a b (i, j) + ((b - a : ℤ) : ZMod m) = orbitMap m a b ((0 : ZMod d₁), j + k₀) := by
  intro j
  simp only [orbitMap, ZMod.val_zero, Nat.cast_zero, zero_mul, zero_add]
  have hpred : (d₁ - 1 + 1 : ℕ) = d₁ := Nat.succ_pred (NeZero.ne d₁)
  -- Step 1: rearrange i.val*(b-a) + j*b + (b-a) = d₁*(b-a) + j*b
  have hcast : (↑i.val : ZMod m) + 1 = (↑d₁ : ZMod m) := by
    rw [hi, ← Nat.cast_one (R := ZMod m), ← Nat.cast_add, hpred]
  have step1 : (↑i.val : ZMod m) * ((b - a : ℤ) : ZMod m) +
      ↑↑j.val * ((b : ℤ) : ZMod m) + ((b - a : ℤ) : ZMod m) =
      (↑d₁ : ZMod m) * ((b - a : ℤ) : ZMod m) + ↑↑j.val * ((b : ℤ) : ZMod m) := by grind
  rw [step1, ← nsmul_eq_mul (d₁), hk₀, nsmul_eq_mul, ← add_mul,
    ← Nat.cast_add (k₀.val) (j.val), ← nsmul_eq_mul, Nat.add_comm]
  -- Reduce (j+k₀) • b mod e₁ using he1_b_zero
  set n := j.val + k₀.val
  have h1 : (j + k₀).val = n % e₁ := ZMod.val_add j k₀
  rw [h1]
  conv_lhs => rw [(Nat.div_add_mod n e₁).symm]
  rw [add_nsmul, mul_nsmul, he1_b_zero, smul_zero, zero_add, nsmul_eq_mul]

/-- In the wrap case, the second coordinate shifts by k₀. -/
private lemma orbitEquiv_snd_shift_ba_wrap [NeZero m]
    {hba_unit : IsUnit ((b - a : ℤ) : ZMod d₁)} (he1_b_zero : e₁ • (b : ZMod m) = 0)
    (k₀ : ZMod e₁) (hk₀ : (d₁ : ℕ) • ((b - a : ℤ) : ZMod m) = (k₀.val : ℕ) • (b : ZMod m))
    (n : ZMod m) (hi : (orbitEquiv hba_unit).symm n |>.1.val = d₁ - 1) :
    ((orbitEquiv hba_unit).symm (n + ↑(b - a))).2 = ((orbitEquiv hba_unit).symm n).2 + k₀ := by
  set Φ := orbitEquiv hba_unit
  set i := (Φ.symm n).1
  set j := (Φ.symm n).2
  have hshift := case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi
  have hn : Φ (i, j) = n := Prod.eta (Φ.symm n) ▸ Equiv.apply_symm_apply Φ n
  have hΦ : Φ ((0 : ZMod d₁), j + k₀) = n + ↑(b - a) := by
    simp only [Φ, orbitEquiv, Equiv.ofBijective_apply] at hn ⊢
    rw [← hn]
    exact (hshift j).symm
  have h : Φ.symm (n + ↑(b - a)) = (0, j + k₀) := by rw [← hΦ, Φ.symm_apply_apply]
  rw [h]

/-- Given d₁ ≥ 3 values each in [u, e₁-u] can sum to any target mod e₁,
    since the range has width ≥ e₁/3 and d₁ ≥ 3. -/
private lemma case2d_rotation_sum_exists {e d : ℕ} [NeZero d]
    (hd_ge : d ≥ 5) (he_ge : e ≥ 19) (he_odd : Odd e) (target : ℕ) :
    ∃ vals : ZMod d → ℕ,
      (∀ i, case2d_u e ≤ vals i ∧ vals i ≤ e - case2d_u e) ∧
      (Finset.univ.sum vals) % e = target % e := by
  have hu_lt : case2d_u e < e := by grind [case2d_u]
  have hdw' : d * (e - 2 * case2d_u e) ≥ e := by
    change d * (e - 2 * (e / 3 + e % 3)) ≥ e
    obtain ⟨k, hk⟩ := he_odd
    subst hk
    have h5w : 5 * ((2 * k + 1) - 2 * ((2 * k + 1) / 3 + (2 * k + 1) % 3)) ≥ 2 * k + 1 := by grind
    exact le_trans h5w (by gcongr)
  set u := case2d_u e
  set w := e - 2 * u
  have hw_pos : 0 < w := by grind
  set deficit := (target + e * d - d * u) % e
  have hdef_lt : deficit < e := Nat.mod_lt _ (by grind)
  set q := deficit / w
  set r := deficit % w
  have hr_lt : r < w := Nat.mod_lt _ hw_pos
  have hq_lt : q < d := by
    by_contra! hge
    have h1 : deficit ≥ d * w :=
      calc deficit ≥ deficit / w * w := Nat.div_mul_le_self deficit w
        _ = q * w := rfl
        _ ≥ d * w := by gcongr
    grind
  have hqr : w * q + r = deficit := Nat.div_add_mod deficit w
  let f : ZMod d → ℕ := fun i => if i.val < q then e - u else if i.val = q then u + r else u
  refine ⟨f, fun i => ?_, ?_⟩
  · grind
  · let g : ZMod d → ℕ := fun i =>
      if i.val < q then w else if i.val = q then r else 0
    have hfg : ∀ i : ZMod d, f i = u + g i := by grind
    have hsum_f : Finset.univ.sum f = d * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, ZMod.card]
    have hcard_lt : (Finset.univ.filter (fun i : ZMod d => i.val < q)).card = q := by
      have : Finset.image ZMod.val (Finset.univ.filter (fun i : ZMod d => i.val < q)) =
          Finset.range q := by
        ext j
        simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
        exact ⟨fun ⟨_, hx, he⟩ => he ▸ hx, fun hj => ⟨(j : ZMod d),
          by rwa [ZMod.val_natCast_of_lt (lt_trans hj hq_lt)],
          ZMod.val_natCast_of_lt (lt_trans hj hq_lt)⟩⟩
      rw [← Finset.card_image_of_injective _ (ZMod.val_injective _), this, Finset.card_range]
    have hcard_eq : (Finset.univ.filter (fun i : ZMod d => i.val = q)).card = 1 := by
      have : Finset.univ.filter (fun i : ZMod d => i.val = q) = {(q : ZMod d)} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => ZMod.val_injective _ (by rwa [ZMod.val_natCast_of_lt hq_lt]),
          fun h => by rw [h, ZMod.val_natCast_of_lt hq_lt]⟩
      rw [this, Finset.card_singleton]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have : ∀ i : ZMod d,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by grind
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        smul_eq_mul, hcard_lt, hcard_eq, one_mul]
    rw [hsum_f, hsum_g, Nat.mul_comm q w, hqr]
    simp only [deficit]
    rw [Nat.add_mod_mod]
    rw [Nat.add_sub_cancel' (le_add_left (le_trans (Nat.mul_le_mul_left d (le_of_lt hu_lt))
      (by rw [Nat.mul_comm]))), Nat.add_mul_mod_self_left]

/-- Splitting a ZMod filter sum at a boundary -/
private lemma zmod_filter_sum_succ {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1)).sum f =
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i := by
  have hsplit : Finset.univ.filter (fun k : ZMod n => k.val < i.val + 1) =
      Finset.univ.filter (fun k : ZMod n => k.val < i.val) ∪ {i} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    grind [ZMod.val_injective]
  grind

/-- When i is the max element, {k | k < i} ∪ {i} = univ. -/
private lemma zmod_filter_sum_last {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n)
    (hi : i.val = n - 1) : (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by rw [← zmod_filter_sum_succ f i]; congr 1; grind

-- Position arithmetic helpers for case2d_coloring_works (not important individually)

/-- Position shift by 1: adding 1 to ZMod coordinate shifts position by 1 mod n. -/
private lemma pos_shift_one {n : ℕ} [NeZero n] (j : ZMod n) (c : ℕ) :
    ((j + 1).val + c) % n = ((j.val + c) % n + 1) % n := by
  rw [ZMod.val_add_one, Nat.mod_add_mod, Nat.mod_add_mod]
  grind

/-- (j + (S + V) % n) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_succ' (j S V n : ℕ) :
    (j + (S + V) % n) % n = ((j + S % n) % n + V) % n := by
  have h1 : j + (S + V) = j + S + V := by grind
  have h2 : (j + S) % n = (j + S % n) % n := (Nat.add_mod_mod j S n).symm
  rw [Nat.add_mod_mod, h1, ← Nat.mod_add_mod (j + S) n V, h2]

/-- Wrap case: if (S + V) % n = k₀ % n, then (j + k₀) % n = ((j + S % n) % n + V) % n -/
private lemma pos_shift_wrap' (j S V k₀ n : ℕ) (hsum : (S + V) % n = k₀ % n) :
    (j + k₀) % n = ((j + S % n) % n + V) % n := by
  rw [← Nat.add_mod_mod j k₀ n, ← hsum, pos_shift_succ']

/-- **Subcase (2d) assembled.** Constructs the coloring for the case when both d₁
    and e₁ are odd with e₁ ≥ 19, using rotated interval patterns. -/
private lemma case2d_coloring_works (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (hd1_odd : Odd d₁) (he1_odd : Odd e₁)
    (he1_ge : e₁ ≥ 19) (h3 : ¬ (3 ∣ d₁)) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  haveI : NeZero m := ⟨by grind⟩
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  have he1_b_zero : e₁ • (b : ZMod m) = 0 :=
    addOrderOf_b_eq (b := b) (m := m) ▸ addOrderOf_nsmul_eq_zero _
  let Φ := orbitEquiv hba_unit
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hba_unit
  have hd1_ge5 : d₁ ≥ 5 := by grind
  obtain ⟨vals, hvals_bound, hvals_sum⟩ := case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
  let rot : ZMod d₁ → ℕ := fun i =>
    ((Finset.univ.filter (fun j : ZMod d₁ => j.val < i.val)).sum vals) % e₁
  let f : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
    basePattern e₁ ((j.val + rot i) % e₁)
  exact orbit_coloring_polychrom Φ orbitEquiv_shift_b orbitEquiv_cycle_shift f (fun n k => by
    set i := (Φ.symm n).1
    set j := (Φ.symm n).2
    set j' := (Φ.symm (n + ↑(b - a))).2
    set p := (j.val + rot i) % e₁ with hp_def
    have hp_lt : p < e₁ := Nat.mod_lt _ (NeZero.pos e₁)
    have covers := basePattern_rotation_covers he1_odd he1_ge
      (hvals_bound i).1 (hvals_bound i).2 hp_lt k
    simp only [Finset.mem_insert, Finset.mem_singleton] at covers
    suffices hpos : (j'.val + rot (i + 1)) % e₁ = (p + vals i) % e₁ by
      rcases covers with h | h | h | h
      · left; exact h
      · right; left; rw [h]; simp only [f]; congr 1; exact (pos_shift_one j (rot i)).symm
      · right; right; left; rw [h]; simp only [f]; congr 1; exact hpos.symm
      · right; right; right
        rw [h]
        simp only [f]
        congr 1
        calc (p + vals i + 1) % e₁
            = ((p + vals i) % e₁ + 1) % e₁ := (Nat.mod_add_mod (p + vals i) e₁ 1).symm
          _ = ((j'.val + rot (i + 1)) % e₁ + 1) % e₁ := by rw [hpos]
          _ = ((j' + 1 : ZMod e₁).val + rot (i + 1)) % e₁ :=
              (pos_shift_one j' (rot (i + 1))).symm
    by_cases hi : i.val + 1 < d₁
    · have hj'_eq : j' = j := orbitEquiv_snd_shift_ba n hi
      rw [hj'_eq]
      change (j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < (i + 1).val)).sum vals) % e₁) % e₁ =
        ((j.val + ((Finset.univ.filter
        (fun k : ZMod d₁ => k.val < i.val)).sum vals) % e₁) % e₁ + vals i) % e₁
      have : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      rw [this, zmod_filter_sum_succ vals i]
      exact pos_shift_succ' j.val _ (vals i) e₁
    · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
      have hj'_eq : j' = j + k₀ :=
        orbitEquiv_snd_shift_ba_wrap he1_b_zero k₀ hk₀ n hi_eq
      rw [hj'_eq]
      have hi1_zero : (i + 1 : ZMod d₁) = 0 :=
        ZMod.val_injective _ (by rw [ZMod.val_add_one, hi_eq, ZMod.val_zero]; grind [Nat.mod_self])
      have hrot0 : rot (0 : ZMod d₁) = 0 := by simp [rot, ZMod.val_zero]
      rw [hi1_zero, hrot0, Nat.add_zero, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁
        (by rw [zmod_filter_sum_last vals i hi_eq, hvals_sum]))

-- Mod 3 arithmetic: (a % e₁ + b) % 3 = (a + b) % 3 when 3 ∣ e₁
private lemma case2c_mod3 (h3e : 3 ∣ e₁) (x y : ℕ) : (x % e₁ + y) % 3 = (x + y) % 3 := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd x h3e, ← Nat.add_mod]

/-- **Subcase (2c):** d₁ and e₁ are both odd, with e₁ ≤ 17 and 3 ∣ e₁.
    Uses shifted periodic 012-patterns with different shifts for adjacent cycles. -/
lemma case_two_odd_small (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) (hd1_odd : Odd d₁) (he1_div3 : 3 ∣ e₁) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  have hm_eq := m_eq_d₁_mul_e₁ (m := m) (b := b)
  haveI : NeZero m := ⟨by grind⟩
  have hba_unit := isUnit_intCast_of_natAbs_coprime (ba_coprime_d1 h_gcd_coprime)
  have he1_b_zero : e₁ • (b : ZMod m) = 0 :=
    addOrderOf_b_eq (b := b) (m := m) ▸ addOrderOf_nsmul_eq_zero _
  let Φ := orbitEquiv hba_unit
  obtain ⟨k₀, hk₀⟩ := case2d_wrap_shift hba_unit
  have hd1_ge3 : d₁ ≥ 3 := by grind
  let f : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
    ⟨(j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3, Nat.mod_lt _ (by grind)⟩
  exact orbit_coloring_polychrom Φ orbitEquiv_shift_b orbitEquiv_cycle_shift f (fun n k => by
    set i := (Φ.symm n).1
    set j := (Φ.symm n).2
    set j' := (Φ.symm (n + ↑(b - a))).2
    set p := case2c_pattern d₁ k₀.val i.val
    by_cases hi : i.val + 1 < d₁
    · have hj'_eq : j' = j := orbitEquiv_snd_shift_ba n hi
      rw [hj'_eq]
      set p' := case2c_pattern d₁ k₀.val (i + 1).val
      have hi'_eq : (i + 1).val = i.val + 1 := by rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hi
      have hhyp : (j.val + p.val) % 3 ≠ (j.val + p'.val) % 3 := by
        change (j.val + (case2c_pattern d₁ k₀.val i.val).val) % 3 ≠
          (j.val + (case2c_pattern d₁ k₀.val (i + 1).val).val) % 3
        rw [hi'_eq]; exact case2c_nonwrap_hyp d₁ k₀.val i.val j.val hd1_ge3 hd1_odd hi
      have hp : p = case2c_pattern d₁ k₀.val i.val := rfl
      have hp' : p' = case2c_pattern d₁ k₀.val (i.val + 1) := by simp [p', hi'_eq]
      rcases cover_mod3_general p p' j.val j.val hhyp k with h | h | h | h
      · left; exact h
      · right; left
        rw [h, hp]
        exact Fin.ext (by simp [f, ZMod.val_add_one, case2c_mod3 he1_div3])
      · right; right; left; exact h
      · right; right; right
        rw [h, hp']
        exact Fin.ext (by
          simp [f, ZMod.val_add_one, case2c_mod3 he1_div3, Nat.mod_eq_of_lt hi])
    · have hi_eq : i.val = d₁ - 1 := by grind [ZMod.val_lt]
      have hj'_eq : j' = j + k₀ :=
        orbitEquiv_snd_shift_ba_wrap he1_b_zero k₀ hk₀ n hi_eq
      rw [hj'_eq]
      set p₀ := case2c_pattern d₁ k₀.val 0
      have hp_eq : p = case2c_pattern d₁ k₀.val (d₁ - 1) := by grind
      have hhyp : (j.val + p.val) % 3 ≠ (j.val + k₀.val + p₀.val) % 3 := by
        rw [hp_eq]; exact case2c_wrap_hyp d₁ k₀.val j.val hd1_ge3 hd1_odd
      have hj'_val : (j + k₀).val = (j.val + k₀.val) % e₁ := ZMod.val_add j k₀
      have hi1_val : (i + 1).val = 0 := by rw [ZMod.val_add_one, hi_eq]; grind [Nat.mod_self]
      have hp : p = case2c_pattern d₁ k₀.val i.val := rfl
      have hp₀_val : (↑p₀ : ℕ) = ↑(case2c_pattern d₁ k₀.val 0) := rfl
      rcases cover_mod3_general p p₀ j.val (j.val + k₀.val) hhyp k with h | h | h | h
      · left; exact h
      · right; left
        rw [h, hp]
        exact Fin.ext (by simp [f, ZMod.val_add_one, case2c_mod3 he1_div3])
      · right; right; left
        rw [h]
        refine Fin.ext ?_
        simp only [f, hi1_val]
        rw [hj'_val]
        exact (case2c_mod3 he1_div3 (j.val + k₀.val) p₀.val).symm
      · right; right; right
        rw [h]
        refine Fin.ext ?_
        simp only [f, hi1_val, ZMod.val_add_one]
        rw [hj'_val, hp₀_val]
        simp only [case2c_mod3 he1_div3, Nat.add_assoc])

/-- Auxiliary: rules out both cycle lengths being ≤ 17 when m ≥ 289. -/
private lemma no_both_e_small {m' d d' : ℕ} (hm : m' ≥ 289) (hcop : Nat.gcd d d' = 1)
    (hd_gt1 : d > 1) (hd'_gt1 : d' > 1) (hd_dvd : d ∣ m') (hd'_dvd : d' ∣ m')
    (he_le : m' / d ≤ 17) (he'_le : m' / d' ≤ 17) : False := by
  have hprod := Nat.le_of_dvd (by grind)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by rwa [Nat.Coprime]) hd_dvd hd'_dvd)
  have h₁ : m' ≤ d * 17 := by rw [← Nat.mul_div_cancel' hd_dvd]; gcongr
  have h₂ : m' ≤ d' * 17 := by rw [← Nat.mul_div_cancel' hd'_dvd]; gcongr
  have := Nat.le_of_mul_le_mul_left (hprod.trans h₁) (by grind)
  have := Nat.le_of_mul_le_mul_left (mul_comm d d' ▸ hprod.trans h₂) (by grind)
  -- 289 ≤ m ≤ d₁*17 → d₁ ≥ 17; similarly d₂ ≥ 17
  -- So d₁ = d₂ = 17, gcd(17,17) = 17 ≠ 1.
  grind

/-! ### Aggregation of Case 2 -/

/-- **Main Case 2 (Multiple Cycles).** Aggregates all subcases (2a)–(2d).
    First applies WLOG to ensure 3 ∤ d₁, then dispatches on parity of d₁ and e₁. -/
lemma main_case_two (hm : m ≥ 289) (h_gcd_coprime : Nat.gcd d₁ d₂ = 1)
    (h_min : min d₁ d₂ > 1) :
    HasPolychromColouring (Fin 3) (zmod_set m a b) := by
  rcases Nat.even_or_odd e₁ with he | ho
  · exact case_two_e1_even hm h_gcd_coprime h_min he
  · rcases Nat.even_or_odd d₁ with hd | hd
    · exact case_two_d1_even_e1_odd hm h_gcd_coprime h_min hd ho
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
        by_cases h3 : 3 ∣ d₁
        · -- Swap roles of b and b-a
          rw [← zmod_set_swap m a b]
          set a' := (-a : ℤ)
          set b' := (b - a : ℤ)
          have hba_eq : (b' - a').natAbs = b.natAbs := by grind
          have hcop' : (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 := by grind
          have hmin' : min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 := by grind
          have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
            intro h3d'; have := Nat.dvd_gcd h3 h3d'
            grind
          rcases Nat.even_or_odd (m / Nat.gcd b'.natAbs m) with he' | ho'
          · exact case_two_e1_even hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b'.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd hm hcop' hmin' hd' ho'
            · exact dispatch a' b' hcop' hmin' hd' ho' h3'
        · exact dispatch a b h_gcd_coprime h_min hd ho h3
      -- Prove dispatch: given ¬(3 ∣ d₁), split on e₁ size
      intro a' b' hcop hmin hd₁_odd he₁_odd h3_nd₁
      set d := Nat.gcd b'.natAbs m
      set d₂' := Nat.gcd (b' - a').natAbs m
      set e := m / d
      have hd_dvd : d ∣ m := Nat.gcd_dvd_right _ _
      have hd₂_dvd : d₂' ∣ m := Nat.gcd_dvd_right _ _
      by_cases he_le : e ≤ 17
      · -- Case 2c: prove 3 ∣ e
        -- Since gcd(d,d₂')=1 and 3 ∤ d, if 3 ∣ d₂' then 3 ∣ m hence 3 ∣ e.
        -- If 3 ∤ d₂': swap and show e₂ ≥ 19 (contradiction with both ≤ 17).
        by_cases h3d₂ : 3 ∣ d₂'
        · have h3m : 3 ∣ m := dvd_trans h3d₂ hd₂_dvd
          have h3e : 3 ∣ e :=
            ((Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3_nd₁).dvd_of_dvd_mul_left
              (Nat.mul_div_cancel' hd_dvd ▸ h3m)
          exact case_two_odd_small hm hcop hmin hd₁_odd h3e
        · -- 3 ∤ d and 3 ∤ d₂ and e ≤ 17: swap and show new e ≥ 19.
          -- After swap, new e₁' = m/d₂. If e₁' ≤ 17 too, contradiction.
          rw [← zmod_set_swap m a' b']
          set a'' := (-a' : ℤ)
          set b'' := (b' - a' : ℤ)
          have hba_eq : (b'' - a'').natAbs = b'.natAbs := by grind
          have hcop' : (Nat.gcd b''.natAbs m).gcd (Nat.gcd (b'' - a'').natAbs m) = 1 := by grind
          have hmin' : min (Nat.gcd b''.natAbs m) (Nat.gcd (b'' - a'').natAbs m) > 1 := by grind
          -- Dispatch on parity
          rcases Nat.even_or_odd (m / Nat.gcd b''.natAbs m) with he' | ho'
          · exact case_two_e1_even hm hcop' hmin' he'
          · rcases Nat.even_or_odd (Nat.gcd b''.natAbs m) with hd' | hd'
            · exact case_two_d1_even_e1_odd hm hcop' hmin' hd' ho'
            · -- Both odd after swap. Show e₁' ≥ 19 by contradiction.
              have he₁'_ge : m / Nat.gcd b''.natAbs m ≥ 19 := by
                by_contra hlt; push_neg at hlt
                rw [Nat.gcd_comm] at hcop
                exact no_both_e_small hm hcop (by grind) (by grind) hd₂_dvd hd_dvd (by grind) he_le
              exact case2d_coloring_works hm hcop' hmin' hd' ho' he₁'_ge h3d₂
      · have he_ge : e ≥ 19 := by grind
        exact case2d_coloring_works hm hcop hmin hd₁_odd he₁_odd he_ge h3_nd₁

end OrbitFramework

end Case2_MultipleCycles
