import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc
import Mathlib.Algebra.Ring.AddAut

/-!
# Combinatorial case analysis for the polychromatic coloring theorem

This file contains the core combinatorial argument for the polychromatic coloring theorem
for 4-element sets. Specifically, it proves that every 4-element subset of ℤ admits a
3-polychromatic coloring under the normalization assumptions described below.

Following the reduction in `Main.lean`, we assume the set $S = \{0, a, b, c\}$ is normalized
such that $0 < a < b < c$, $a + b \le c$, $c \ge 289$, and $\gcd(a, b, c) = 1$.
The proof works in the cyclic group $\mathbb{Z}_m$ where $m = c - a + b$.
As shown in §4 of the paper, the polychromaticity of $S$ in $\mathbb{Z}$ follows from
its polychromaticity in $\mathbb{Z}_m$.

## Main results

- `normal_bit` — **the main theorem**: every normalized 4-element set admits a
  3-polychromatic coloring. This is the entry point used by `Main.lean`.

## Proof structure

Let $d_1 = \gcd(b, m)$ and $d_2 = \gcd(b{-}a, m)$. The proof dispatches on whether
one of these GCDs equals 1 (so the corresponding element generates all of
$\mathbb{Z}_m$) or both are greater than 1 (so $\mathbb{Z}_m$ decomposes into
shorter cycles):

- `main_case_one` — **Case 1: Single Cycle (§4.1).**
  Applies when $\min(d_1, d_2) = 1$. The set reduces to $\{0,1,g,g{+}1\}$ via an
  affine transformation (`exists_g_of_coprime`). Subcases by the gap parameter $g$:
  - `case_one_small_g` — **(1a)** $g \in \{2,3,4\}$, via Table 1 block colorings.
  - `case_one_interval` — **(1b)** General $g$, via interval coloring.
  - `case_one_residues` — **(1c)** $3 \nmid m$, via multiplication by 3.
  - `case_one_divisible` — **(1d)** $3 \mid m$, via explicit periodic colorings.

- `main_case_two` — **Case 2: Multiple Cycles (§4.2).**
  Applies when both $d_1, d_2 > 1$. Setting $e_1 = m/d_1$, we use the isomorphism
  $\mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \cong \mathbb{Z}_m$ to define colorings
  cycle-by-cycle. Subcases by the parity of $d_1$ and $e_1$:
  - `case_two_e1_even` — **(2a)** $e_1$ even: parity-based alternation.
  - `case_two_d1_even_e1_odd` — **(2b)** $d_1$ even, $e_1$ odd: alternation with fixup.
  - `case_two_odd_small` — **(2c)** Both odd, $e_1 \le 17$: shifted periodic colorings.
  - `case2d_coloring_works` — **(2d)** Both odd, $e_1 \ge 19$: rotating interval patterns.

## File organization

The file is organized into Lean `section`s:

- `BlockColorInfra` — General tool (`blockColor_polychrom`) for proving polychromaticity
  of cyclic colorings formed by concatenating two block sizes.
- `Table1` — Concrete block colorings for six specific 4-element sets.
- `Case1_SingleCycle` — Case 1 subcases (1a)–(1d) and their aggregation.
- `Case2_MultipleCycles` — Case 2 subcases (2a)–(2d) and their aggregation.
- `Assembly` — Glue connecting the $\mathbb{Z}_m$ analysis back to $\mathbb{Z}$,
  culminating in `normal_bit`.

Most `private` lemmas are modular arithmetic helpers or case-analysis plumbing.

-/

open Finset Pointwise

/-! ## Preliminaries: the normalized set in ZMod m -/

/--
A helper to define the transformed set in ZMod m.
Corresponds to S = {0, b-a, b, 2b-a} in the informal text.
-/
def zmod_set (m : ℕ) (a b : ℤ) : Finset (ZMod m) :=
  ({0, b - a, b, 2 * b - a} : Finset ℤ).image Int.cast

/-- Auxiliary: the polychromatic number is invariant under the translation that
    maps `{0, a, b, c}` to `zmod_set m a b`. -/
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
    grind [sub_add_eq_add_sub, two_mul]
  rw [this, polychromNumber_vadd]

/-- The set {0, b-a, b, 2b-a} is symmetric in the two repeated differences b and b-a:
    swapping them (replacing a by -a, b by b-a) gives the same set. -/
lemma zmod_set_swap (m : ℕ) (a b : ℤ) : zmod_set m (-a) (b - a) = zmod_set m a b := by
  grind [zmod_set]

/-! ## Block coloring infrastructure

Given blocks A (length r) and B (length r+1), concatenate h copies of A followed
by k copies of B to color ℤ_m where m = r·h + (r+1)·k. Polychromaticity reduces
to checking 4 block-pair boundaries (AA, AB, BA, BB), which is decidable for
concrete blocks. The key result is `blockColor_polychrom` at the end of this section.

The remaining lemmas in this section are technical plumbing.
-/

section BlockColorInfra

/--
Check that every starting position in the list `L` hits all three colors {0, 1, 2}
when considering the provided `offsets`.
This is a "linear" check because it doesn't account for cyclic wrap-around;
that is handled by checking all possible block-pair concatenations.
-/
def checkLinearPolychrom (offsets : List ℕ) (L : List (Fin 3)) : Bool :=
  let maxOff := offsets.foldr max 0
  (List.range (L.length - maxOff)).all fun i => ([0, 1, 2] : List (Fin 3)).all fun c =>
      offsets.any fun s => L[i + s]? == some c

/--
Verifies that the block-based coloring remains polychromatic across all possible
transitions between blocks `A` and `B`.
Specifically, it checks the four possible concatenations: AA, AB, BA, and BB.
If these four "local" checks pass, then any sequence of these blocks will
produce a polychromatic coloring.
-/
def checkBlockPairs (offsets : List ℕ) (A B : List (Fin 3)) : Bool :=
  checkLinearPolychrom offsets (A ++ A) &&
  checkLinearPolychrom offsets (A ++ B) &&
  checkLinearPolychrom offsets (B ++ A) &&
  checkLinearPolychrom offsets (B ++ B)

/--
The coloring function generated by concatenating `h` copies of block `A`
followed by some copies of block `B`.
The resulting pattern colors $\mathbb{Z}_m$ where $m = h|A| + k|B|$.
-/
def blockColorVal (A B : List (Fin 3)) (h : ℕ) (p : ℕ) : Fin 3 :=
  if p < A.length * h then (A[p % A.length]?).getD 0
  else (B[(p - A.length * h) % B.length]?).getD 0


private lemma checkLinearPolychrom_spec {offsets : List ℕ} {L : List (Fin 3)}
    (hcheck : checkLinearPolychrom offsets L = true)
    {i : ℕ} (hi : i + offsets.foldr max 0 < L.length) (c : Fin 3) :
    ∃ s ∈ offsets, L[i + s]? = some c := by
  simp only [checkLinearPolychrom, List.all_eq_true, List.mem_range, List.any_eq_true,
    beq_iff_eq] at hcheck
  exact hcheck i (by omega) c (by fin_cases c <;> simp)

/-- Frobenius representation for consecutive block sizes r, r+1:
    any m ≥ r(r-1) can be written as r·h + (r+1)·k. -/
private lemma frobenius_consec {rA m : ℕ} (hrA : 1 < rA) (hm : m ≥ rA * (rA - 1)) :
    ∃ h k, rA * h + (rA + 1) * k = m ∧ 0 < h + k := by
  obtain ⟨a, b, hab⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le rA (rA + 1) m
    (by rw [(Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).gcd_eq_one]; exact one_dvd _)
    (by grind [Nat.pred_eq_sub_one, mul_comm rA (rA - 1)])
  refine ⟨a, b, by grind [mul_comm a rA, mul_comm b (rA + 1)], ?_⟩
  by_contra hle; push_neg at hle
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  subst ha0; subst hb0; simp only [zero_mul, zero_add] at hab; subst hab
  have : 0 < rA * (rA - 1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- Bridge: a cyclic coloring function yields HasPolychromColouring. -/
private lemma hasPolychromColouring_of_cyclic {m : ℕ} [NeZero m] [Fact (1 < m)]
    (c : ℕ → Fin 3) (S : Finset (ZMod m))
    (hpoly : ∀ n : ZMod m, ∀ k : Fin 3, ∃ a ∈ S, c (n + a).val = k) :
    HasPolychromColouring (Fin 3) S :=
  ⟨fun x => c x.val, hpoly⟩


/-- If `i % r + s < r`, then `(i + s) % r = i % r + s`. -/
private lemma add_mod_of_lt {i s r : ℕ} (h : i % r + s < r) : (i + s) % r = i % r + s := by
  have hs : s < r := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hs]
  exact Nat.mod_eq_of_lt h

/-- If `r ≤ i % r + s < 2r`, then `(i + s) % r = i % r + s - r`. -/
private lemma add_mod_sub {i s r : ℕ} (hr : 0 < r) (hge : r ≤ i % r + s)
    (hlt : i % r + s < 2 * r) :
    (i + s) % r = i % r + s - r := by
  have h1 := Nat.mod_add_div i r
  have h2 := Nat.mod_lt i hr
  have key : i + s = (i % r + s - r) + (i / r + 1) * r := by
    grind [Nat.sub_add_cancel hge, mul_comm r (i / r)]
  conv_lhs => rw [key]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- If `M ≤ n` and `n - M < M`, then `n % M = n - M`. -/
private lemma mod_eq_sub {n M : ℕ} (hge : M ≤ n) (hlt : n - M < M) : n % M = n - M := by
  conv_lhs => rw [← Nat.sub_add_cancel hge]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

/-- If `i < r * n` and `i % r + s < r`, then `i + s < r * n`. -/
private lemma add_lt_of_mod_add_lt {i s r n : ℕ} (hr : 0 < r)
    (hi : i < r * n) (h : i % r + s < r) :
    i + s < r * n := by
  have h1 := Nat.mod_add_div i r
  have h2 := Nat.mod_lt i hr
  have h3 : i / r < n := Nat.div_lt_of_lt_mul hi
  have : i / r + 1 ≤ n := by omega
  grind [Nat.mul_le_mul_left r this]

/-- If `r * (n-1) ≤ i` and `r ≤ i % r + s`, then `r * n ≤ i + s`. -/
private lemma ge_mul_of_mod_add_ge {i s r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hi_lo : r * (n - 1) ≤ i) (hge : r ≤ i % r + s) :
    r * n ≤ i + s := by
  have := Nat.mod_add_div i r
  have := Nat.mod_lt i hr
  have : n - 1 ≤ i / r := by
    rw [Nat.le_div_iff_mul_le hr]; grind
  have : n ≤ i / r + 1 := by omega
  grind [Nat.mul_le_mul_left r this]

/-! ### Bridge lemmas

These connect list indexing (`XY[js]?`) to `blockColorVal`: if the list element
equals the appropriate block element, the list element equals the coloring value.
-/

/-- If `XY[js]? = A[idx]?` and `p` is in the A-region with `p % |A| = idx`,
    then `XY[js]? = some (blockColorVal A B h p)`. -/
private lemma bcv_eq_A (A B : List (Fin 3)) (h : ℕ)
    (XY : List (Fin 3)) (js p idx : ℕ)
    (hp : p < A.length * h)
    (hmod : p % A.length = idx) (hidx : idx < A.length)
    (hxy : XY[js]? = A[idx]?) :
    XY[js]? = some (blockColorVal A B h p) := by
  rw [hxy, List.getElem?_eq_getElem hidx]
  simp only [blockColorVal, if_pos hp]
  rw [hmod, List.getElem?_eq_getElem hidx, Option.getD_some]

/-- If `XY[js]? = B[idx]?` and `p` is in the B-region with
    `(p - |A|*h) % |B| = idx`, then `XY[js]? = some (blockColorVal A B h p)`. -/
private lemma bcv_eq_B (A B : List (Fin 3)) (h : ℕ)
    (XY : List (Fin 3)) (js p idx : ℕ)
    (hp : ¬(p < A.length * h))
    (hmod : (p - A.length * h) % B.length = idx) (hidx : idx < B.length)
    (hxy : XY[js]? = B[idx]?) :
    XY[js]? = some (blockColorVal A B h p) := by
  rw [hxy, List.getElem?_eq_getElem hidx]
  simp only [blockColorVal, if_neg hp]
  rw [hmod, List.getElem?_eq_getElem hidx, Option.getD_some]

/-- When `i = j + q` and `j + s ≥ r`, then `i + s - (q + r) = j + s - r`. -/
private lemma sub_add_eq {i j s r q : ℕ} (hge : r ≤ j + s)
    (hi : j + q = i) :
    i + s - (q + r) = j + s - r := by grind

/-- When i is in the last block before boundary `r*h`, and j = i%r: `i + s - r*h = j + s - r`. -/
private lemma sub_region_eq {i s r h : ℕ} (hr : 0 < r)
    (hi_lo : r * (h - 1) ≤ i) (hi_hi : i < r * h)
    (hjs_ge : r ≤ i % r + s) :
    i + s - r * h = i % r + s - r := by
  have hdiv := Nat.mod_add_div i r
  have hle : h - 1 ≤ i / r := by rw [Nat.le_div_iff_mul_le hr]; grind
  have hlt : i / r < h := Nat.div_lt_of_lt_mul (by grind)
  have hh : 1 ≤ h := by omega
  have hQr : r * h = r * (i / r) + r := by grind [Nat.sub_add_cancel]
  rw [hQr]
  exact sub_add_eq hjs_ge hdiv

/-! ### Common goal type for each case

`CaseGoal A B offsets h m i` asserts that there exists a block pair `XY` and
a starting index `j` in `XY` such that `checkLinearPolychrom` passes and every
offset `s` maps to the correct `blockColorVal` value. Each case lemma below
produces a `CaseGoal`, and the main theorem dispatches to them.
-/

/-- The common proof obligation for each case of `blockColor_polychrom`. -/
private def CaseGoal (A B : List (Fin 3)) (offsets : List ℕ) (h m i : ℕ) : Prop :=
  ∃ (XY : List (Fin 3)) (j : ℕ),
    checkLinearPolychrom offsets XY = true ∧
    j + offsets.foldr max 0 < XY.length ∧
    ∀ s, s ≤ offsets.foldr max 0 → XY[j + s]? = some (blockColorVal A B h ((i + s) % m))

/-! ### Case 1: No wrap, AA interior -/
private lemma case_no_wrap_AA (A B : List (Fin 3)) (offsets : List ℕ)
    (h k m i : ℕ)
    (hA : 0 < A.length)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAA : checkLinearPolychrom offsets (A ++ A) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (h_AA : i + offsets.foldr max 0 < A.length * h) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  refine ⟨A ++ A, j, hAA, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  have his_A : i + s < A.length * h := by grind
  by_cases hjs_lt : j + s < A.length
  · exact bcv_eq_A A B h _ _ _ _ his_A
      (add_mod_of_lt hjs_lt) hjs_lt (List.getElem?_append_left hjs_lt)
  · push_neg at hjs_lt
    have hjs_sub : j + s - A.length < A.length := by grind
    have hjs_2r : i % A.length + s < 2 * A.length := by grind
    exact bcv_eq_A A B h _ _ _ _ his_A
      (add_mod_sub hA hjs_lt hjs_2r) hjs_sub
      (by rw [List.getElem?_append_right (by grind)])

/-! ### Case 2: No wrap, AB boundary -/
private lemma case_no_wrap_AB (A B : List (Fin 3)) (offsets : List ℕ)
    (h k m i : ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAB : checkLinearPolychrom offsets (A ++ B) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (hA_region : i < A.length * h)
    (h_cross : A.length * h ≤ i + offsets.foldr max 0) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  have hh_pos : 0 < h := by grind
  have hi_lo : A.length * (h - 1) ≤ i := by grind [Nat.mul_sub]
  refine ⟨A ++ B, j, hAB, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  by_cases hjs_lt : j + s < A.length
  · exact bcv_eq_A A B h _ _ _ _
      (add_lt_of_mod_add_lt hA hA_region hjs_lt)
      (add_mod_of_lt hjs_lt) hjs_lt
      (List.getElem?_append_left hjs_lt)
  · push_neg at hjs_lt
    have hjs_B : j + s - A.length < B.length := by grind
    have his_ge : A.length * h ≤ i + s := ge_mul_of_mod_add_ge hA hh_pos hi_lo hjs_lt
    have hnot_A : ¬(i + s < A.length * h) := by grind
    refine bcv_eq_B A B h _ _ _ _ hnot_A ?_ hjs_B ?_
    · rw [sub_region_eq hA hi_lo hA_region hjs_lt,
        Nat.mod_eq_of_lt (by grind)]
    · rw [List.getElem?_append_right (by grind)]

/-! ### Case 3: No wrap, BB -/
private lemma case_no_wrap_BB (A B : List (Fin 3)) (offsets : List ℕ)
    (h k m i : ℕ)
    (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBB : checkLinearPolychrom offsets (B ++ B) = true)
    (hm : A.length * h + B.length * k = m)
    (h_no_wrap : i + offsets.foldr max 0 < m)
    (hB_region : A.length * h ≤ i) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  set j := (i - A.length * h) % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  refine ⟨B ++ B, j, hBB, by grind, fun s hsle => ?_⟩
  rw [Nat.mod_eq_of_lt (by grind)]
  by_cases hjs_lt : j + s < B.length
  · exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_of_lt hjs_lt)
      hjs_lt (List.getElem?_append_left hjs_lt)
  · push_neg at hjs_lt
    have hjs_sub : j + s - B.length < B.length := by grind
    exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_sub (by grind) hjs_lt (by grind))
      hjs_sub
      (by rw [List.getElem?_append_right (by grind)])

/-! ### Case 4: Wrap, A region (k = 0) -/
private lemma case_wrap_A (A B : List (Fin 3)) (offsets : List ℕ)
    (h m i : ℕ)
    (hA : 0 < A.length)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hAA : checkLinearPolychrom offsets (A ++ A) = true)
    (hm : A.length * h = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hA_region : i < A.length * h) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  subst hm
  set j := i % A.length
  have hj_lt : j < A.length := Nat.mod_lt _ hA
  have hh_pos : 0 < h := by grind
  have hi_lo : A.length * (h - 1) ≤ i := by grind [Nat.mul_sub]
  have hAh : A.length ≤ A.length * h := Nat.le_mul_of_pos_right _ hh_pos
  refine ⟨A ++ A, j, hAA, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < A.length
  · have his_lt : i + s < A.length * h := add_lt_of_mod_add_lt hA (by grind) hjs_lt
    rw [Nat.mod_eq_of_lt his_lt]
    exact bcv_eq_A A B h _ _ _ _ his_lt
      (add_mod_of_lt hjs_lt) hjs_lt (List.getElem?_append_left hjs_lt)
  · push_neg at hjs_lt
    have his_ge : A.length * h ≤ i + s := ge_mul_of_mod_add_ge hA hh_pos hi_lo hjs_lt
    have hmod : (i + s) % (A.length * h) = i + s - A.length * h := mod_eq_sub his_ge (by grind)
    have hsub_eq := sub_region_eq hA hi_lo (by grind) hjs_lt
    have hjs_idx : j + s - A.length < A.length := by grind
    refine bcv_eq_A A B h _ _ _ _ (by grind)
      (by rw [hmod, Nat.mod_eq_of_lt (by grind), hsub_eq])
      hjs_idx ?_
    rw [List.getElem?_append_right (by grind)]

/-! ### Case 5: Wrap, B region, h > 0 → BA -/
private lemma case_wrap_BA (A B : List (Fin 3)) (offsets : List ℕ)
    (h k m i : ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBA : checkLinearPolychrom offsets (B ++ A) = true)
    (hm : A.length * h + B.length * k = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hB_region : A.length * h ≤ i)
    (hh_pos : 0 < h) (hk_pos : 0 < k) :
    CaseGoal A B offsets h m i := by
  set maxOff := offsets.foldr max 0
  have hAh : A.length ≤ A.length * h := Nat.le_mul_of_pos_right _ hh_pos
  have hBk : B.length ≤ B.length * k := Nat.le_mul_of_pos_right _ hk_pos
  set j := (i - A.length * h) % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  have hi_B : i - A.length * h < B.length * k := by grind
  have hk_lo : B.length * (k - 1) ≤ i - A.length * h := by grind [Nat.mul_sub]
  refine ⟨B ++ A, j, hBA, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < B.length
  · -- Still in B
    have his_lt : (i - A.length * h) + s < B.length * k :=
      add_lt_of_mod_add_lt (by grind) hi_B hjs_lt
    rw [Nat.mod_eq_of_lt (by grind)]
    exact bcv_eq_B A B h _ _ _ _ (by grind)
      (by rw [Nat.sub_add_comm hB_region]; exact add_mod_of_lt hjs_lt)
      hjs_lt (List.getElem?_append_left hjs_lt)
  · -- Wrapped to A region
    push_neg at hjs_lt
    have his_ge : m ≤ i + s := by
      have := ge_mul_of_mod_add_ge (by grind) hk_pos hk_lo hjs_lt
      grind
    have hmod : (i + s) % m = i + s - m := mod_eq_sub his_ge (by grind)
    have hsub_eq : i + s - m = j + s - B.length := by
      have := sub_region_eq (by grind) hk_lo hi_B hjs_lt
      grind
    have hjs_idx : j + s - B.length < A.length := by grind
    refine bcv_eq_A A B h _ _ _ _ (by grind)
      (by rw [hmod, Nat.mod_eq_of_lt (by grind), hsub_eq])
      hjs_idx ?_
    rw [List.getElem?_append_right (by grind)]

/-! ### Case 6: Wrap, B region, h = 0 → BB -/
private lemma case_wrap_BB (A B : List (Fin 3)) (offsets : List ℕ)
    (k m i : ℕ)
    (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hBB : checkLinearPolychrom offsets (B ++ B) = true)
    (hm : B.length * k = m)
    (hi : i < m)
    (h_wrap : m ≤ i + offsets.foldr max 0)
    (hk_pos : 0 < k) :
    CaseGoal A B offsets 0 m i := by
  set maxOff := offsets.foldr max 0
  have hBk : B.length ≤ B.length * k := Nat.le_mul_of_pos_right _ hk_pos
  set j := i % B.length
  have hj_lt : j < B.length := Nat.mod_lt _ (by grind)
  have hk_lo : B.length * (k - 1) ≤ i := by grind [Nat.mul_sub]
  refine ⟨B ++ B, j, hBB, by grind, fun s hsle => ?_⟩
  by_cases hjs_lt : j + s < B.length
  · have his_lt : i + s < B.length * k := add_lt_of_mod_add_lt (by grind) (by grind) hjs_lt
    rw [Nat.mod_eq_of_lt (by grind)]
    exact bcv_eq_B A B 0 _ _ _ _
      (by omega)
      (by grind [add_mod_of_lt hjs_lt])
      hjs_lt (List.getElem?_append_left hjs_lt)
  · push_neg at hjs_lt
    have his_ge : m ≤ i + s := by
      have := ge_mul_of_mod_add_ge (by grind) hk_pos hk_lo hjs_lt
      grind
    have hmod : (i + s) % m = i + s - m := mod_eq_sub his_ge (by grind)
    have hsub_eq : i + s - m = j + s - B.length := by
      rw [← hm]
      exact sub_region_eq (by grind) hk_lo (by grind) hjs_lt
    have hjs_idx : j + s - B.length < B.length := by grind
    refine bcv_eq_B A B 0 _ _ _ _
      (by omega)
      (by rw [Nat.mul_zero, Nat.sub_zero, hmod, Nat.mod_eq_of_lt (by grind), hsub_eq])
      hjs_idx ?_
    rw [List.getElem?_append_right (by grind)]

/-! ### Main result of the block coloring infrastructure -/

/-- **Key infrastructure theorem.** If all block-pair checks pass, the block coloring is
    polychromatic for any m expressible as rA·h + rB·k. This is the main interface
    used by the Table 1 lemmas below. -/
theorem blockColor_polychrom
    (A B : List (Fin 3)) (offsets : List ℕ)
    (hA : 0 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hpairs : checkBlockPairs offsets A B = true)
    {h k : ℕ} (hhk : 0 < h + k) {m : ℕ}
    (hm : A.length * h + B.length * k = m)
    {i : ℕ} (hi : i < m) (c : Fin 3) :
    ∃ s ∈ offsets, blockColorVal A B h ((i + s) % m) = c := by
  set maxOff := offsets.foldr max 0
  simp only [checkBlockPairs, Bool.and_eq_true] at hpairs
  obtain ⟨⟨⟨hAA, hAB⟩, hBA⟩, hBB⟩ := hpairs
  -- Reduce to CaseGoal
  suffices hg : CaseGoal A B offsets h m i by
    obtain ⟨XY, j, hXY_check, hj_bound, hcorr⟩ := hg
    obtain ⟨s, hs_mem, hs_eq⟩ := checkLinearPolychrom_spec hXY_check hj_bound c
    refine ⟨s, hs_mem, ?_⟩
    have := hcorr s (List.le_max_of_le' 0 hs_mem le_rfl)
    rw [hs_eq] at this; exact Option.some.inj this.symm
  -- Dispatch to case lemmas
  by_cases h_wrap : i + maxOff < m
  · by_cases hA_region : i < A.length * h
    · by_cases h_cross : i + maxOff < A.length * h
      · exact case_no_wrap_AA A B offsets h k m i hA hmaxOff hAA hm h_wrap h_cross
      · push_neg at h_cross
        have hk_pos : 0 < k := by grind
        exact case_no_wrap_AB A B offsets h k m i hA hBlen hmaxOff hAB hm h_wrap hA_region h_cross
    · push_neg at hA_region
      exact case_no_wrap_BB A B offsets h k m i hBlen hmaxOff hBB hm h_wrap hA_region
  · push_neg at h_wrap
    by_cases hA_region : i < A.length * h
    · have hk0 : k = 0 := by rw [hBlen] at hm; nlinarith [hmaxOff]
      subst hk0; simp only [mul_zero, add_zero] at hm
      exact case_wrap_A A B offsets h m i hA hmaxOff hAA hm hi h_wrap hA_region
    · push_neg at hA_region
      have hk_pos : 0 < k := by nlinarith [hm, hA_region, hi]
      by_cases hh_pos : 0 < h
      · exact case_wrap_BA A B offsets h k m i hA hBlen hmaxOff
          hBA hm hi h_wrap hA_region hh_pos hk_pos
      · have hh0 : h = 0 := by grind
        subst hh0
        simp only [mul_zero, zero_add] at hm
        exact case_wrap_BB A B offsets k m i hBlen hmaxOff hBB hm hi h_wrap hk_pos

end BlockColorInfra

/-! ## Table 1: Block concatenation colorings (paper §4, Table 1)

Each `table1_*` lemma constructs a concrete 3-polychromatic coloring for a specific
4-element set using `blockColor_polychrom`. These are intermediate results used in
subcases (1a) and (1c) of Case 1.

| Lemma | Set | Block size r | Min m |
|-------|-----|-------------|-------|
| `table1_0123` | {0,1,2,3} | 3 | 6 |
| `table1_0134` | {0,1,3,4} | 6 | 30 |
| `table1_0235` | {0,2,3,5} | 6 | 30 |
| `table1_0347` | {0,3,4,7} | 9 | 72 |
| `table1_0358` | {0,3,5,8} | 9 | 72 |
| `table1_0145` | {0,1,4,5} | 7 | 42 |
-/

section Table1

variable (m : ℕ)

/-- Helper to convert block coloring polychromaticity into HasPolychromColouring
    for a specific finset of offsets in ZMod m. -/
private lemma table1_of_blockColor (A B : List (Fin 3)) (offsets : List ℕ)
    (S : Finset (ZMod m))
    (hA : 2 < A.length) (hBlen : B.length = A.length + 1)
    (hmaxOff : offsets.foldr max 0 ≤ A.length)
    (hpairs : checkBlockPairs offsets A B = true)
    (hm : m ≥ A.length * (A.length - 1))
    (hS : ∀ a : ZMod m, a ∈ S ↔ ∃ s ∈ offsets, (s : ZMod m) = a) :
    HasPolychromColouring (Fin 3) S := by
  have hA_lt_m : A.length < m := by
    have : A.length * 2 ≤ A.length * (A.length - 1) := by gcongr; omega
    omega
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  obtain ⟨h, k, hm_eq, hhk⟩ := frobenius_consec (by omega : 1 < A.length) hm
  have hm_eq' : A.length * h + B.length * k = m := by rw [hBlen]; exact hm_eq
  apply hasPolychromColouring_of_cyclic (blockColorVal A B h) S
  intro n target
  obtain ⟨s, hs_mem, hs_eq⟩ := blockColor_polychrom A B offsets (by omega) hBlen hmaxOff
    hpairs hhk hm_eq' (ZMod.val_lt n) target
  refine ⟨(s : ZMod m), (hS _).mpr ⟨s, hs_mem, rfl⟩, ?_⟩
  have : s < m := lt_of_le_of_lt (le_trans (List.le_max_of_le' 0 hs_mem le_rfl) hmaxOff) hA_lt_m
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt this]
  exact hs_eq

/-- {0,1,2,3}: blocks [0,1,2] (r=3), [0,0,1,2] (r+1=4). Frobenius bound: m ≥ 6. -/
lemma table1_0123 (hm : m ≥ 6) : HasPolychromColouring (Fin 3) ({0, 1, 2, 3} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,1,2] [0,0,1,2] [0,1,2,3]
    {0, 1, 2, 3} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

/-- {0,1,3,4}: blocks [0,0,1,2,1,2] (r=6), [0,0,0,1,2,1,2] (r+1=7). Frobenius: m ≥ 30. -/
lemma table1_0134 (hm : m ≥ 30) : HasPolychromColouring (Fin 3) ({0, 1, 3, 4} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,1,2,1,2] [0,0,0,1,2,1,2] [0,1,3,4]
    {0, 1, 3, 4} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

/-- {0,2,3,5}: blocks [0,0,1,1,2,2] (r=6), [0,0,0,1,1,2,2] (r+1=7). Frobenius: m ≥ 30. -/
lemma table1_0235 (hm : m ≥ 30) : HasPolychromColouring (Fin 3) ({0, 2, 3, 5} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,1,1,2,2] [0,0,0,1,1,2,2] [0,2,3,5]
    {0, 2, 3, 5} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

/-- {0,3,4,7}: blocks [0,0,0,1,1,1,2,2,2] (r=9), [0,0,0,0,1,1,1,2,2,2] (r+1=10).
    Frobenius: m ≥ 72. -/
lemma table1_0347 (hm : m ≥ 72) : HasPolychromColouring (Fin 3) ({0, 3, 4, 7} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,0,1,1,1,2,2,2] [0,0,0,0,1,1,1,2,2,2] [0,3,4,7]
    {0, 3, 4, 7} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

/-- {0,3,5,8}: blocks [0,0,0,1,1,1,2,2,2] (r=9), [0,0,0,0,1,1,1,2,2,2] (r+1=10).
    Frobenius: m ≥ 72. -/
lemma table1_0358 (hm : m ≥ 72) : HasPolychromColouring (Fin 3) ({0, 3, 5, 8} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,0,1,1,1,2,2,2] [0,0,0,0,1,1,1,2,2,2] [0,3,5,8]
    {0, 3, 5, 8} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

/-- {0,1,4,5}: blocks [0,0,0,1,2,1,2] (r=7), [0,0,0,0,1,2,1,2] (r+1=8). Frobenius: m ≥ 42. -/
lemma table1_0145 (hm : m ≥ 42) : HasPolychromColouring (Fin 3) ({0, 1, 4, 5} : Finset (ZMod m)) :=
  table1_of_blockColor m [0,0,0,1,2,1,2] [0,0,0,0,1,2,1,2] [0,1,4,5]
    {0, 1, 4, 5} (by simp) (by simp) (by decide) (by decide) hm
    (by intro a; simp; tauto)

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
private lemma phase_ne_of_gap {s j₀ jg : ℕ} (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by
  obtain ⟨t, ht⟩ := hs3; subst ht
  have hqlt : (jg + 3 * t - j₀) / (3 * t) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hdam := Nat.div_add_mod (jg + 3 * t - j₀) (3 * t)
  rcases hgap with hmod | hmod <;>
    rcases lt_two' _ hqlt with hq | hq <;>
    rw [hq, hmod] at hdam
  · grind [Nat.mul_add_mod]
  · grind
  · grind [Nat.mul_add_mod]
  · grind

open Finpartition in
private lemma idx_in_interval' (s m : ℕ) (hs : 0 < s) (hs_le : s ≤ m)
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
      grind [Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
    grind
  split
  · rename_i hlt
    set j := p / (q + 1)
    have hq1_pos : 0 < q + 1 := by omega
    have hj_lt_r : j < r := by
      rw [Nat.div_lt_iff_lt_mul hq1_pos]; exact hlt
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
    have hd_lt : d < s - r := by
      rw [Nat.div_lt_iff_lt_mul hq_pos]; omega
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
private lemma gap_exceeds_ilen (m s g : ℕ) (hs : 0 < s)
    (h_lb : (m + s - 1) / s < g) (j : ℕ) :
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
private lemma shift_within_two' (m s g : ℕ)
    (h_ub : g < 2 * (m / s))
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
private lemma idx_range_from_endpoints' (m s : ℕ)
    (a b p : ℕ)
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
private lemma gap_bound_interval (s g m : ℕ) (hs : 0 < s)
    (hs3 : 3 ≤ s) (hs_le : s ≤ m)
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
    have hep_diff :
        Finpartition.equiEndpoint m s (j₀ + 3) - m =
        q * (j₀ + 3 - s) := by
      rw [hep_j3, hm_eq]; grind [Nat.mul_add]
    have hvgm_ub : v + g - m < Finpartition.equiEndpoint m s
          (j₀ + 3 - s) := by
      have : v + g - m < q * (j₀ + 3 - s) := by
        rw [← hep_diff]; omega
      have : q * (j₀ + 3 - s) ≤ Finpartition.equiEndpoint m s
            (j₀ + 3 - s) := by
        change q * (j₀ + 3 - s) ≤ q * (j₀ + 3 - s) + min r (j₀ + 3 - s)
        omega
      omega
    have hrange := idx_range_from_endpoints' m s
      0 (j₀ + 3 - s) (v + g - m)
      (by unfold Finpartition.equiEndpoint; simp)
      hvgm_ub jg hvg_lo hvg_hi
    have : jg + s - j₀ = 1 ∨ jg + s - j₀ = 2 := by
      omega
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
  have hsub : s * q + r - r * (q + 1) = (s - r) * q := by
    zify [hle, (by omega : r ≤ s)]; ring
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

private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) :
    eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by
  unfold eqp_idx
  split_ifs with h1 h2
  · exact div_step p (q + 1) (by omega)
  · omega
  · right
    have hpeq : p + 1 = r * (q + 1) := by omega
    have hr_pos : 0 < r := by grind
    have h_succ : (p + 1) / (q + 1) = r := by
      rw [hpeq]; exact Nat.mul_div_cancel r (by omega)
    have hne : p / (q + 1) ≠ r := by
      intro heq
      grind [Nat.div_mul_le_self p (q + 1)]
    have hidx_p : p / (q + 1) = r - 1 := by
      have := div_step p (q + 1) (by omega); omega
    rw [hpeq, Nat.sub_self, Nat.zero_div, hidx_p]; omega
  · have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by
      omega
    rw [hsub]
    have := div_step (p - r * (q + 1)) q hq; omega

-- Helper: if quotient stays same, remainder increases by 1
private lemma mod_step (a b : ℕ)
    (h : (a + 1) / b = a / b) :
    (a + 1) % b = a % b + 1 := by
  grind [Nat.div_add_mod a b, Nat.div_add_mod (a + 1) b]

-- Helper: if quotient increases by 1, remainder resets to 0
private lemma mod_zero_step (a b : ℕ) (hb : 0 < b)
    (h : (a + 1) / b = a / b + 1) :
    (a + 1) % b = 0 := by
  have h1 := Nat.div_add_mod a b
  have h2 := Nat.div_add_mod (a + 1) b
  have h3 := Nat.mod_lt a hb
  have h4 : b * ((a + 1) / b) = b * (a / b) + b := by grind
  grind

private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;>
      by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1, if_pos h2]
    apply mod_step p (q + 1)
    have h3 : eqp_idx q r (p + 1) = (p + 1) / (q + 1) := by
      unfold eqp_idx; rw [if_pos h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by
      unfold eqp_idx; rw [if_pos h2]
    grind
  · omega
  · exfalso
    have h3 : eqp_idx q r (p + 1) = r + (p + 1 - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by
      unfold eqp_idx; rw [if_pos h2]
    have h5 : p / (q + 1) < r := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h2
    have h6 : r ≤ eqp_idx q r (p + 1) := by
      rw [h3]; exact Nat.le_add_right r _
    grind
  · rw [if_neg h1, if_neg h2]
    have hsub : p + 1 - r * (q + 1) = (p - r * (q + 1)) + 1 := by omega
    rw [hsub]
    apply mod_step (p - r * (q + 1)) q
    have h3 : eqp_idx q r (p + 1) = r + (p + 1 - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h1]
    have h4 : eqp_idx q r p = r + (p - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h2]
    rw [h3, h4, hsub] at h; omega

private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) ≠ eqp_idx q r p) :
    eqp_off q r (p + 1) = 0 := by
  unfold eqp_off
  by_cases h1 : p + 1 < r * (q + 1) <;>
      by_cases h2 : p < r * (q + 1)
  · rw [if_pos h1]
    apply mod_zero_step p (q + 1) (by omega)
    have h3 : eqp_idx q r (p + 1) = (p + 1) / (q + 1) := by
      unfold eqp_idx; rw [if_pos h1]
    have h4 : eqp_idx q r p = p / (q + 1) := by
      unfold eqp_idx; rw [if_pos h2]
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
    have h4 : eqp_idx q r p = r + (p - r * (q + 1)) / q := by
      unfold eqp_idx; rw [if_neg h2]
    rw [h3, h4, hsub] at h
    have := div_step (p - r * (q + 1)) q hq
    omega

private lemma gap_mod_cases_gen (s j₀ jg d : ℕ)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hmod : (jg + s - j₀) % s = d) :
    jg + s - j₀ = d ∨ jg + s - j₀ = s + d := by
  have hd_hi : jg + s - j₀ < 2 * s := by omega
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  rw [hmod] at hdiv
  have hq_lt : (jg + s - j₀) / s < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h <;> grind

private lemma equiEndpoint_diff_ge (m s j : ℕ) : m / s ≤ Finpartition.equiEndpoint m s (j + 1) -
        Finpartition.equiEndpoint m s j := by
  grind [Finpartition.equiEndpoint]

open Finpartition in
private lemma straddle1_gap2 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
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
  have hv_eq : v + 1 = equiEndpoint m s (j₀ + 1) := by
    omega
  have hjg_cases := gap_mod_cases_gen s j₀ jg 1 hj₀_lt hjg_lt hgap1
  have hq_pos : 0 < m / s := by
    grind
  have hg_lt_m : g < m := by
    have := Nat.div_mul_le_self m s; nlinarith
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
private lemma straddle2_gap1 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ≤ s) (hs_le : s ≤ m)
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
  have hq_pos : 0 < m / s := by
    grind
  have hg_lt_m : g < m := by
    have := Nat.div_mul_le_self m s; nlinarith
  have hjg_cases := gap_mod_cases_gen s j₀ jg 2 hj₀_lt hjg_lt hgap2
  have hep0 : equiEndpoint m s 0 = 0 := by
    simp [equiEndpoint]
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
      rw [hj₀_eq2] at hv_hi
      rw [Nat.sub_add_cancel (by omega), hep_s] at hv_hi
      have hd1 := equiEndpoint_diff_ge m s 0
      rw [hep0, Nat.zero_add] at hd1
      have hd2 := equiEndpoint_diff_ge m s 1
      have hmono12 : equiEndpoint m s 1 ≤ equiEndpoint m s (1 + 1) := by omega
      have hsac12 := Nat.sub_add_cancel hmono12
      omega

private lemma eqp_idx_succ_lt_m (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (hm_eq : m = s * q + r)
    (hp : p < m) :
    p + 1 < m ∨ eqp_idx q r (p + 1) = s := by
  by_cases h : p + 1 < m
  · exact Or.inl h
  · have hpm : p + 1 = m := by omega
    right
    rw [hpm, hm_eq]
    exact eqp_idx_m q r s hq_pos hr_lt

private lemma non_straddle_witness (q r p : ℕ)
    (hq_pos : 0 < q)
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

private lemma straddle_boundary_color (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s)
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
    have hm_idx : eqp_idx q r m = s := by
      rw [hm_eq]; exact eqp_idx_m q r s hq_pos hr_lt
    have hjs : j + 1 = s := by rw [hj]; omega
    grind

private lemma vg_mod_shift (v g d : ℕ) : (v + (g + d)) % m = ((v + g) % m + d) % m := by
  grind [Nat.add_mod (v + g) d m, Nat.add_mod ((v + g) % m) d m,
    Nat.mod_mod_of_dvd _ (dvd_refl m)]

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
  have hq_pos : 0 < q := by
    nlinarith [Nat.div_mul_le_self m s, h_lb, h_ub]
  have hs_le : s ≤ m := by nlinarith [Nat.div_mul_le_self m s]
  have hg1_lt_m : g + 1 < m := by
    nlinarith [Nat.div_mul_le_self m s, Nat.le_of_dvd hs hs3]
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
          have : (s - r) * q + r * q = s * q := by
            grind [Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
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
  -- Step 1: which pair covers k?
  have : (k.val = j₀ % 3 ∨ k.val = (j₀ + 1) % 3) ∨
      (k.val = jg % 3 ∨ k.val = (jg + 1) % 3) := by omega
  rcases this with hk1 | hk2
  · -- Pair 1 covers k: k ∈ {j₀%3, (j₀+1)%3}
    rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
    · -- Pair 1 non-straddle
      have hv1_lt : v + 1 < m := by
        rcases eqp_idx_succ_lt_m m q r s v hq_pos hr_lt hm_eq hv_lt with h | h
        · exact h
        · rw [h1_same] at h
          have : j₀ = s := h; omega
      obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r v
        hq_pos hv_lt hv1_lt h1_same j₀ rfl k.val hk1
      exact ⟨d, by simp only [Finset.mem_insert,
        Finset.mem_singleton] at hd_mem ⊢; omega, hd_eq⟩
    · -- Pair 1 straddles → gap = 2
      open Finpartition in
      have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
      have hgap2 := straddle1_gap2 s g m hs hs3_le hs_le h_lb
        h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi hvg_lo
        hvg_hi hstrad1 hgap
      have hjg1_eq : (jg + 1) % 3 = j₀ % 3 := by
        grind [gap_mod_cases_gen]
      rcases hk1 with hk_eq | hk_eq
      · -- k = j₀%3 = (jg+1)%3: pair 2 must be non-straddle
        rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
        · -- Pair 2 non-straddle → witness a = g+d
          have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
          have hvg1_lt : (v + g) % m + 1 < m := by
            rcases eqp_idx_succ_lt_m m q r s ((v + g) % m) hq_pos hr_lt hm_eq hvg_lt with h | h
            · exact h
            · rw [h2_same] at h
              have : jg = s := h; omega
          obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r
            ((v + g) % m) hq_pos hvg_lt hvg1_lt h2_same jg rfl
            k.val (Or.inr (hk_eq ▸ hjg1_eq.symm))
          refine ⟨g + d, ?_, ?_⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hd_mem ⊢; omega
          · change (idx ((v + (g + d)) % m) + off ((v + (g + d)) % m) % 2) % 3 = k.val
            rw [vg_mod_shift m v g d]; exact hd_eq
        · -- Pair 2 straddles → contradiction: gap = 1
          open Finpartition in
          have hstrad2 : equiEndpoint m s (jg + 1) ≤ (v + g) % m + 1 :=
            endpoint_bridge ((v + g) % m) (Nat.mod_lt _ (by omega)) hjg_lt h2_step
          have hgap1 := straddle2_gap1 s g m hs hs3_le hs_le
            h_lb h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi
            hvg_hi hstrad2 hgap
          omega
      · -- k = (j₀+1)%3: witness a = 1
        refine ⟨1, by simp, ?_⟩
        change (eqp_idx q r ((v + 1) % m) + eqp_off q r ((v + 1) % m) % 2) % 3 = k.val
        rw [straddle_boundary_color m q r s v hq_pos hr_lt hs3 hm_eq hv_lt h1_step j₀ rfl]
        exact hk_eq.symm
  · -- Pair 2 covers k: k ∈ {jg%3, (jg+1)%3}
    rcases eqp_idx_step q r ((v + g) % m) hq_pos with h2_same | h2_step
    · -- Pair 2 non-straddle
      have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
      have hvg1_lt : (v + g) % m + 1 < m := by
        rcases eqp_idx_succ_lt_m m q r s ((v + g) % m) hq_pos hr_lt hm_eq hvg_lt with h | h
        · exact h
        · rw [h2_same] at h
          have : jg = s := h; omega
      obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r
        ((v + g) % m) hq_pos hvg_lt hvg1_lt h2_same jg rfl
        k.val hk2
      refine ⟨g + d, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hd_mem ⊢; omega
      · change (idx ((v + (g + d)) % m) + off ((v + (g + d)) % m) % 2) % 3 = k.val
        rw [vg_mod_shift m v g d]; exact hd_eq
    · -- Pair 2 straddles → gap = 1
      have hvg_lt : (v + g) % m < m := Nat.mod_lt _ (by omega)
      open Finpartition in
      have hstrad2 : equiEndpoint m s (jg + 1) ≤
          (v + g) % m + 1 := endpoint_bridge ((v + g) % m) hvg_lt hjg_lt h2_step
      have hgap1 := straddle2_gap1 s g m hs hs3_le hs_le h_lb
        h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_lo hv_hi
        hvg_hi hstrad2 hgap
      have hj01_eq : (j₀ + 1) % 3 = jg % 3 := by
        grind [gap_mod_cases_gen]
      rcases hk2 with hk_eq | hk_eq
      · -- k = jg%3 = (j₀+1)%3: pair 1 non-straddle
        rcases eqp_idx_step q r v hq_pos with h1_same | h1_step
        · -- Pair 1 non-straddle → witness a = d
          have hv1_lt : v + 1 < m := by
            rcases eqp_idx_succ_lt_m m q r s v hq_pos hr_lt hm_eq hv_lt with h | h
            · exact h
            · rw [h1_same] at h
              have : j₀ = s := h; omega
          obtain ⟨d, hd_mem, hd_eq⟩ := non_straddle_witness m q r
            v hq_pos hv_lt hv1_lt h1_same j₀ rfl k.val
            (Or.inr (hk_eq ▸ hj01_eq.symm))
          exact ⟨d, by simp only [Finset.mem_insert,
            Finset.mem_singleton] at hd_mem ⊢; omega, hd_eq⟩
        · -- Pair 1 straddles → contradiction: gap = 2
          open Finpartition in
          have hstrad1 : equiEndpoint m s (j₀ + 1) ≤ v + 1 := endpoint_bridge v hv_lt hj₀_lt h1_step
          have hgap2 := straddle1_gap2 s g m hs hs3_le hs_le
            h_lb h_ub v j₀ jg hv_lt hj₀_lt hjg_lt hv_hi
            hvg_lo hvg_hi hstrad1 hgap
          omega
      · -- k = (jg+1)%3: witness a = g+1
        refine ⟨g + 1, by simp, ?_⟩
        change (idx ((v + (g + 1)) % m) + off ((v + (g + 1)) % m) % 2) % 3 = k.val
        rw [vg_mod_shift m v g 1]
        change (eqp_idx q r (((v + g) % m + 1) % m) + eqp_off q r (((v + g) % m + 1) % m) % 2) % 3 =
          k.val
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
lemma case_one_res_3g_sub_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 2) :
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
lemma case_one_res_3g_sub_1 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g - 1) :
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
lemma case_one_res_3g_add_1 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 1) :
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
lemma case_one_res_3g_add_2 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 2) :
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
lemma case_one_res_3g_add_4 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 4) :
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
lemma case_one_res_3g_add_5 (g : ℕ) (hm : m ≥ 289)
    (hg : m = 3 * g + 5) :
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
lemma case_one_div_g_not_three (g : ℕ)
    (h_div : m = 3 * g ∨ m = 3 * g + 3)
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
    have : (g : ZMod 3) = ↑(g % 3 : ℕ) := by
      rw [ZMod.natCast_mod]
    simp only [this, h]; decide
  }

/-- (1d), m = 3g, g ≡ 0 (mod 3): diagonal coloring `n ↦ (n%3 + n/g) % 3`. -/
lemma case_one_div_3g (g : ℕ) (hm_eq : m = 3 * g)
    (hg3 : 3 ∣ g) (hg : 0 < g) :
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
    have h2 : p = p % (3 * g) + 3 * (p / (3 * g)) * g := by
      grind [Nat.mod_add_div p (3 * g)]
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
    have hp_eq : p = h * (3 * (p / (3 * h))) + p % (3 * h) := by
      grind [Nat.mod_add_div p (3 * h)]
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
lemma case_one_dispatch (g : ℕ) (hm : m ≥ 289) (hg_ge : 2 ≤ g)
    (hg_le : g ≤ m / 2) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
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

private lemma isUnit_intCast_of_natAbs_coprime {n : ℕ} {b : ℤ}
    (h : Nat.gcd b.natAbs n = 1) :
    IsUnit (Int.cast b : ZMod n) := by
  have hu : IsUnit (b.natAbs : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq b with hb | hb
  · have : (Int.cast b : ZMod n) = ↑b.natAbs := by rw [hb]; simp
    rwa [this]
  · have : (Int.cast b : ZMod n) = -↑b.natAbs := by rw [hb]; simp
    rw [this]; exact hu.neg

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
  have hbg'1 : bz * (g' + 1) = 2 * bz - az := by
    rw [mul_add, mul_one, hbg']; ring
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
    grind [Finset.card_le_card hsub,
      Finset.card_le_three (a := (0 : ZMod m)) (b := 1) (c := g')]
  · conv at hset => rhs; rw [← hval]
    exact hset

/-- **Main Case 1 (Single Cycle).** Aggregates all subcases (1a)–(1d).
    Reduces to {0,1,g,g+1} via `exists_g_of_coprime`, applies WLOG g ≤ m/2,
    then dispatches via `case_one_dispatch`. -/
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

/-! ### Arithmetic helpers for cycle decomposition

These lemmas set up the orbit map infrastructure. They are not important individually
but are used throughout Case 2.
-/

private lemma intCast_2ba_eq :
    ((2 * b - a : ℤ) : ZMod m) = ((b - a : ℤ) : ZMod m) + ((b : ℤ) : ZMod m) := by
  push_cast; ring

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

/--
A coloring for Case 2a ($e_1$ even).
Each cycle $i$ uses two colors that alternate based on position parity.
Cycles are assigned "missing colors" such that no two adjacent cycles miss the same color.
-/
private def cycle_coloring (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → Fin 3 := fun ⟨i, j⟩ =>
  if i.val = d₁ - 1 ∧ ¬Even d₁ then ⟨1 + j.val % 2, by grind⟩
  else if i.val % 2 = 0 then ⟨j.val % 2, by grind⟩
  else ⟨2 * (j.val % 2), by grind⟩

/-- The "missing" color for each cycle category in Case 2a. -/
private def missing_color (d₁ : ℕ) (i : ZMod d₁) : Fin 3 :=
  if i.val = d₁ - 1 ∧ d₁ % 2 = 1 then 0
  else if i.val % 2 = 0 then 2
  else 1

-- Fin 3 fact: if a ≠ b, a ≠ c, b ≠ c, and k ≠ c, then k = a ∨ k = b.
private lemma fin3_eq_of_ne {a b c k : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hkc : k ≠ c) :
    k = a ∨ k = b := by
  grind [Fin.ext_iff]

-- cycle_coloring(i, j) never equals the missing color of cycle i.
private lemma f_ne_missing_color (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (i : ZMod d₁) (j : ZMod e₁) :
    cycle_coloring d₁ e₁ (i, j) ≠ missing_color d₁ i := by
  grind [cycle_coloring, missing_color, Fin.ext_iff]

-- Adjacent cycles have different missing colors.
private lemma missing_color_ne_succ (d₁ : ℕ) [NeZero d₁] (hd₁ : d₁ ≥ 2)
    (i : ZMod d₁) : missing_color d₁ i ≠ missing_color d₁ (i + 1) := by
  grind [missing_color, zmod_val_add_one d₁ hd₁ i, Fin.ext_iff]

-- cycle_coloring(i,j) ≠ cycle_coloring(i,j+1) when parity flips.
private lemma f_alt_color (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (hparity : ∀ j : ZMod e₁, j.val % 2 ≠ (j + 1).val % 2)
    (i : ZMod d₁) (j : ZMod e₁) :
    cycle_coloring d₁ e₁ (i, j) ≠ cycle_coloring d₁ e₁ (i, j + 1) := by
  grind [cycle_coloring, Fin.ext_iff]

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

/--
The orbit map $\phi : \mathbb{Z}_{d_1} \times \mathbb{Z}_{e_1} \to \mathbb{Z}_m$ defined by
$\phi(i, j) = i(b-a) + jb \pmod m$. This map is a bijection when $\gcd(b-a, b, m) = 1$.
It provides the coordinate system used to analyze the "Multiple Cycles" case.
-/
private def orbitMap (m : ℕ) (a b : ℤ) (d₁ e₁ : ℕ) : ZMod d₁ × ZMod e₁ → ZMod m :=
  fun p => (p.1.val : ZMod m) * ↑(b - a) + (p.2.val : ZMod m) * ↑b

private lemma addOrderOf_b_eq {m : ℕ} {b : ℤ} {d₁ : ℕ} (hm : 0 < m)
    (hd1_def : Nat.gcd b.natAbs m = d₁) :
    addOrderOf (b : ZMod m) = m / d₁ := by
  have key : addOrderOf (b.natAbs : ZMod m) = m / d₁ := by
    rw [ZMod.addOrderOf_coe b.natAbs (by grind), Nat.gcd_comm, hd1_def]
  rcases Int.natAbs_eq b with h | h
  · have : (b : ZMod m) = (b.natAbs : ZMod m) := by rw [h]; simp
    rw [this]; exact key
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
    have := Nat.eq_zero_of_dvd_of_lt hdvd (by
      grind [j₁.val_lt (n := e₁), j₂.val_lt (n := e₁)])
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
      orbitMap m a b d₁ e₁ p + (b : ZMod m) = orbitMap m a b d₁ e₁ (p.1, p.2 + 1) := by
  intro ⟨i, j⟩
  simp only [orbitMap]
  by_cases hj : j.val + 1 < e₁
  · have hv : (j + 1).val = j.val + 1 := by
      rw [ZMod.val_add_one]; exact Nat.mod_eq_of_lt hj
    rw [hv]; push_cast; ring
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
  rw [this]; push_cast; ring

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
  have key := hΦ (Φ.symm x).1 (Φ.symm x).2
  rw [Equiv.apply_symm_apply] at key
  exact Φ.symm_apply_eq.mpr key.symm

/-- If α(Φ(i,j)) = i for all i,j, then (Φ⁻¹(x)).1 = α(x). -/
private lemma equiv_symm_fst_eq {d₁ e₁ : ℕ} {γ : Type*}
    (Φ : ZMod d₁ × ZMod e₁ ≃ γ) (α : γ → ZMod d₁)
    (hα : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (Φ (i, j)) = i)
    (x : γ) :
    (Φ.symm x).1 = α x := by
  have h := hα (Φ.symm x).1 (Φ.symm x).2
  rw [Equiv.apply_symm_apply] at h; exact h.symm

/-! ### Orbit coloring framework -/

/-- **Key infrastructure for Case 2.** Polychromaticity from an orbit coloring:
    given an orbit equivalence Φ with shift properties and a coloring f,
    if f covers all colors at any translate, then f ∘ Φ.symm is polychromatic.
    All four Case 2 subcases use this as their final step. -/
private lemma orbit_coloring_polychrom {m : ℕ} {a b : ℤ} {d₁ e₁ : ℕ}
    [NeZero m] [NeZero d₁] [NeZero e₁]
    (Φ : ZMod d₁ × ZMod e₁ ≃ ZMod m)
    (hΦ_add_b : ∀ x : ZMod m,
      Φ.symm (x + ↑b) = ((Φ.symm x).1, (Φ.symm x).2 + 1))
    (hΦ_cycle_shift : ∀ x : ZMod m,
      (Φ.symm (x + ↑(b - a))).1 = (Φ.symm x).1 + 1)
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
    have : (n : ZMod m) + ↑(2 * b - a) = (n + ↑(b - a)) + ↑b := by
      rw [intCast_2ba_eq, add_assoc]
    rw [congr_arg χ this]
    have hΦ' := hΦ_add_b (n + ↑(b - a))
    exact congr_arg f (Prod.ext
      (by rw [Prod.ext_iff.mp hΦ' |>.1, hi_shift])
      (Prod.ext_iff.mp hΦ' |>.2))
  rcases hcovers n k with h | h | h | h
  · exact ⟨0, by simp, by rw [add_zero, hχ_n, h]⟩
  · exact ⟨↑b, by simp, by rw [hχ_nb, h]⟩
  · exact ⟨↑(b - a), by simp, by rw [hχ_nba, h]⟩
  · exact ⟨↑(2 * b - a), by simp, by rw [hχ_n2ba, h]⟩

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
  let α : ZMod m → ZMod d₁ :=
    fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
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

/-! ### Subcase (2b) construction: d₁ even, e₁ odd

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
  grind [case2b_coloring, Fin.ext_iff]

-- Lemma 2: Odd cycles never produce color 1.
private lemma case2b_odd_ne_one (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 1) :
    case2b_coloring d₁ e₁ (i, j) ≠ 1 := by
  grind [case2b_coloring, Fin.ext_iff]

-- Lemma 3: Every consecutive pair on an even cycle contains color 1.
private lemma case2b_even_has_one (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 2)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 0) :
    case2b_coloring d₁ e₁ (i, j) = 1 ∨ case2b_coloring d₁ e₁ (i, j + 1) = 1 := by
  grind [case2b_coloring, zmod_val_add_one e₁ he₁ j, Fin.ext_iff]

-- Lemma 4: Every consecutive pair on an odd cycle contains color 2.
private lemma case2b_odd_has_two (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 2)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 1) :
    case2b_coloring d₁ e₁ (i, j) = 2 ∨ case2b_coloring d₁ e₁ (i, j + 1) = 2 := by
  grind [case2b_coloring, zmod_val_add_one e₁ he₁ j, Fin.ext_iff]

-- Lemma 5: Even pair is {1,1} only at j = e₁ − 2.
private lemma case2b_even_degenerate_pos (d₁ e₁ : ℕ) [NeZero d₁] [NeZero e₁]
    (he₁ : e₁ ≥ 3)
    (i : ZMod d₁) (j : ZMod e₁) (hi : i.val % 2 = 0)
    (h1 : case2b_coloring d₁ e₁ (i, j) = 1)
    (h2 : case2b_coloring d₁ e₁ (i, j + 1) = 1) :
    j.val = e₁ - 2 := by
  grind [case2b_coloring, zmod_val_add_one e₁ (by grind : e₁ ≥ 2) j, Fin.ext_iff]

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
  rw [zmod_val_add_one e₁ (by grind) j] at h2
  grind

-- Fin 3 helpers for Case 2b.
private lemma case2b_fin3_eq_one {a : Fin 3} (h0 : a ≠ 0) (h2 : a ≠ 2) : a = 1 := by
  grind [Fin.ext_iff]
private lemma case2b_fin3_eq_two {a : Fin 3} (h0 : a ≠ 0) (h1 : a ≠ 1) : a = 2 := by
  grind [Fin.ext_iff]

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
  have he₁_ge2 : e₁ ≥ 2 := by grind
  have hd₁_ge2 : d₁ ≥ 2 := by have := NeZero.ne d₁; grind
  have hi_parity := parity_flip_even d₁ hd₁_even hd₁_ge2 i
  rcases Nat.even_or_odd i.val with ⟨_, hi_even⟩ | ⟨_, hi_odd⟩
  · -- i is even, i+1 is odd
    have hi : i.val % 2 = 0 := by grind
    have hi1 : (i + 1).val % 2 = 1 := by grind
    fin_cases k
    · -- k = 0: by contradiction via degenerate position argument
      by_contra! h_not
      have hev1 : case2b_coloring d₁ e₁ (i, j₁) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.1 h.symm) (case2b_even_ne_two d₁ e₁ i j₁ hi)
      have hev2 : case2b_coloring d₁ e₁ (i, j₁ + 1) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.2.1 h.symm) (case2b_even_ne_two d₁ e₁ i (j₁ + 1) hi)
      have hod1 : case2b_coloring d₁ e₁ (i + 1, j₂) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.2.1 h.symm) (case2b_odd_ne_one d₁ e₁ (i + 1) j₂ hi1)
      have hod2 : case2b_coloring d₁ e₁ (i + 1, j₂ + 1) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.2.2 h.symm)
          (case2b_odd_ne_one d₁ e₁ (i + 1) (j₂ + 1) hi1)
      have hj1_eq := case2b_even_degenerate_pos d₁ e₁ he₁ i j₁ hi hev1 hev2
      have hj2_eq := case2b_odd_degenerate_pos d₁ e₁ he₁_odd he₁ (i + 1) j₂ hi1 hod1 hod2
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
    have hi : i.val % 2 = 1 := by grind
    have hi1 : (i + 1).val % 2 = 0 := by grind
    fin_cases k
    · -- k = 0: by contradiction
      by_contra! h_not
      have hod1 : case2b_coloring d₁ e₁ (i, j₁) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.1 h.symm) (case2b_odd_ne_one d₁ e₁ i j₁ hi)
      have hod2 : case2b_coloring d₁ e₁ (i, j₁ + 1) = 2 :=
        case2b_fin3_eq_two (fun h => h_not.2.1 h.symm) (case2b_odd_ne_one d₁ e₁ i (j₁ + 1) hi)
      have hev1 : case2b_coloring d₁ e₁ (i + 1, j₂) = 1 :=
        case2b_fin3_eq_one (fun h => h_not.2.2.1 h.symm) (case2b_even_ne_two d₁ e₁ (i + 1) j₂ hi1)
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

/-! ### Subcase (2b) main lemma -/

/-- **Subcase (2b).** $d_1$ is even and $e_1$ is odd.
    Alternating patterns with a "degenerate" position fixup at different positions
    for even and odd cycles, ensuring they do not overlap across adjacent cycles. -/
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
    have : q.natAbs = b.natAbs / d₁ := by
      rw [hq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hd₁_pos]
    rw [this]; exact Nat.coprime_div_gcd_div_gcd hd₁_pos
  -- Define the cycle map φ = orbitMap and derive bijectivity from shared infrastructure
  let φ := orbitMap m a b d₁ e₁
  let Φ := Equiv.ofBijective φ (orbitMap_bijective hm_eq hd₁_dvd hb_zero hba_unit hord)
  have hφ_add_b : ∀ i : ZMod d₁, ∀ j : ZMod e₁,
      φ (i, j + 1) = φ (i, j) + ↑b := by
    intro i j; exact (orbitMap_shift_b he1_b (i, j)).symm
  -- Cycle index function α : ZMod m → ZMod d₁
  obtain ⟨u_ba, hu_ba⟩ := hba_unit
  let α : ZMod m → ZMod d₁ :=
    fun x => ZMod.castHom hd₁_dvd (ZMod d₁) x * u_ba⁻¹
  have hα_ba : ∀ x, α (x + ↑(b - a)) = α x + 1 := cycle_index_shift_ba hd₁_dvd u_ba hu_ba
  have hα_φ : ∀ i : ZMod d₁, ∀ j : ZMod e₁, α (φ (i, j)) = i :=
    orbitMap_cycle_index hd₁_dvd hb_zero u_ba hu_ba
  have hΦ_add_b := equiv_symm_shift_b Φ hφ_add_b
  have hΦ_cycle := equiv_symm_fst_eq Φ α hα_φ
  -- d₂ properties for the compatibility argument
  set d₂ := Nat.gcd (b - a).natAbs m
  have hd₂_dvd : d₂ ∣ m := Nat.gcd_dvd_right _ _
  have hd₂_gt1 : d₂ > 1 := by
    simp only [d₂]; grind
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
  -- π(b) is a unit in ZMod d₂
  have hπ_b_unit : IsUnit (π (↑b)) := by
    change IsUnit ((ZMod.castHom hd₂_dvd (ZMod d₂)) (↑b))
    rw [map_intCast]
    apply isUnit_intCast_of_natAbs_coprime
    -- gcd(b.natAbs, d₂) = 1: since d₂ coprime to d₁, and b = d₁*q with gcd(q,e₁)=1
    rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left h_gcd_coprime (hq_cop.coprime_dvd_right hd₂_dvd_e₁)
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
    have hd₂_dvd_diff : d₂ ∣ (e₁ - 2) := (ZMod.natCast_eq_zero_iff _ _).mp hval_eq.symm
    have hd₂_dvd_2 : d₂ ∣ 2 := by
      have := Nat.dvd_sub hd₂_dvd_e₁ hd₂_dvd_diff
      have : e₁ - (e₁ - 2) = 2 := by grind
      grind
    obtain ⟨k, hk⟩ := hd₂_dvd_e₁
    obtain ⟨l, hl⟩ := he1_odd
    have := Nat.le_of_dvd (by grind) hd₂_dvd_2
    grind
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
        conv_lhs => rw [this]; exact hπ_φ p.1 j
      have hπn' : π n = (j'.val : ZMod d₂) * π (↑b) := by
        rw [← hπ_eq]
        have : n + ↑(b - a) = Φ (Φ.symm (n + ↑(b - a))) := (Equiv.apply_symm_apply Φ _).symm
        conv_lhs => rw [this]; exact hπ_φ _ j'
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

/-! ### Subcase (2d): d₁, e₁ both odd, e₁ ≥ 19

The most technically involved subcase. The base pattern on C₀ uses three
alternating bicolor intervals of sizes u, v, w. Each subsequent cycle is a
rotation of C₀. The many private lemmas below are technical helpers for
verifying the rotation property; the important result is `case2d_coloring_works`.
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


private lemma case2d_uv_le {e₁ : ℕ} (hge : e₁ ≥ 19) : case2d_u e₁ + case2d_v e₁ ≤ e₁ := by
  grind [case2d_u, case2d_v]

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

/-- Consecutive positions (j, j+1) within the same interval produce both colors of that interval. -/
private lemma basePattern_consec_same_interval {e₁ j : ℕ}
    (hsame : whichInterval e₁ j = whichInterval e₁ (j + 1)) :
    {basePattern e₁ j, basePattern e₁ (j + 1)} = intervalColors (whichInterval e₁ j) := by
  simp only [whichInterval, basePattern, intervalColors] at *
  set u := case2d_u e₁
  -- Both j and j+1 are in the same interval; their parities differ
  split_ifs at hsame ⊢ with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  all_goals (ext x; fin_cases x <;>
    simp_all only [Fin.isValue, mem_insert, mem_singleton] <;> grind)

/-- At an interval boundary (j at end, j+1 at start of next), the pair of
    consecutive basePattern values equals the pair of the left interval. -/
private lemma basePattern_consec_boundary {e₁ j : ℕ}
    (he : Odd e₁) (hge : e₁ ≥ 19) (hj : j < e₁)
    (hdiff : whichInterval e₁ j ≠ whichInterval e₁ ((j + 1) % e₁)) :
    {basePattern e₁ j, basePattern e₁ ((j + 1) % e₁)} = intervalColors (whichInterval e₁ j) := by
  obtain ⟨ku, hku⟩ : Odd (case2d_u e₁) := by obtain ⟨k, hk⟩ := he; grind [case2d_u]
  obtain ⟨kv, hkv⟩ : Odd (case2d_v e₁) := by obtain ⟨k, hk⟩ := he; grind [case2d_v]
  obtain ⟨kw, hkw⟩ : Odd (e₁ - case2d_u e₁ - case2d_v e₁) := by
    obtain ⟨k, hk⟩ := he; grind [case2d_u, case2d_v]
  have huv := case2d_uv_le hge
  simp only [whichInterval] at hdiff ⊢
  by_cases hj1_wrap : j + 1 < e₁
  · rw [Nat.mod_eq_of_lt hj1_wrap] at hdiff ⊢
    grind [basePattern, intervalColors]
  · -- Wrap: j = e₁ - 1
    push_neg at hj1_wrap
    have hj_eq : j = e₁ - 1 := by grind
    subst hj_eq
    have : e₁ - 1 + 1 = e₁ := by grind
    rw [this, Nat.mod_self] at hdiff ⊢
    grind [basePattern, intervalColors]

/-- Combined: for any j, {basePattern(j), basePattern(j+1 mod e₁)} is the
    interval pair of whichInterval(j). -/
private lemma basePattern_consec_pair {e₁ j : ℕ}
    (he : Odd e₁) (hge : e₁ ≥ 19) (hj : j < e₁) :
    intervalColors (whichInterval e₁ j) ⊆ {basePattern e₁ j, basePattern e₁ ((j + 1) % e₁)} := by
  by_cases hsame : whichInterval e₁ j = whichInterval e₁ ((j + 1) % e₁)
  · -- Same interval: j+1 < e₁ (otherwise wrap changes interval)
    have hj1 : j + 1 < e₁ := by
      by_contra h
      push_neg at h
      have : j = e₁ - 1 := by grind
      subst this
      have : e₁ - 1 + 1 = e₁ := by grind
      rw [this, Nat.mod_self] at hsame
      grind [whichInterval, case2d_u, case2d_v]
    rw [Nat.mod_eq_of_lt hj1]
    exact (basePattern_consec_same_interval (by rwa [Nat.mod_eq_of_lt hj1] at hsame)).ge
  · exact (basePattern_consec_boundary he hge hj hsame).ge

/-- A rotation by r ∈ [u, e₁-u] moves to a different interval:
    whichInterval(j) ≠ whichInterval((j + r) % e₁). -/
private lemma rotation_changes_interval {e₁ j : ℕ}
    (hge : e₁ ≥ 19) (hj : j < e₁)
    {r : ℕ} (hr_lo : case2d_u e₁ ≤ r) (hr_hi : r ≤ e₁ - case2d_u e₁) :
    whichInterval e₁ j ≠ whichInterval e₁ ((j + r) % e₁) := by
  have he₁_pos : 0 < e₁ := by grind
  have huv_bound := case2d_uv_le hge
  have hv_le_u : case2d_v e₁ ≤ case2d_u e₁ := by grind [case2d_u, case2d_v]
  have hw_le_u : e₁ - (case2d_u e₁ + case2d_v e₁) ≤ case2d_u e₁ := by
    grind [case2d_u, case2d_v]
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
    rw [hmod] at heq hj'_lt
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
  have hq_eta : q = (q.1, q.2) := (Prod.eta q).symm
  rw [hq_eta] at hφq
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
    have hfg : ∀ i : ZMod d₁, f i = u + g i := by
      grind
    have hsum_f : Finset.univ.sum f = d₁ * u + Finset.univ.sum g := by
      conv_lhs => arg 2; ext i; rw [hfg i]
      simp [Finset.sum_add_distrib, Finset.card_univ, ZMod.card]
    have hsum_g : Finset.univ.sum g = q * w + r := by
      have hg_split : ∀ i : ZMod d₁,
          g i = (if i.val < q then w else 0) + (if i.val = q then r else 0) := by
        grind
      rw [Finset.sum_congr rfl (fun i _ => hg_split i), Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          smul_eq_mul]
        congr 1
        trans (Finset.image ZMod.val (Finset.univ.filter (fun i : ZMod d₁ => i.val < q))).card
        · rw [Finset.card_image_of_injective _ (ZMod.val_injective _)]
        · have : Finset.image ZMod.val
              (Finset.univ.filter (fun i : ZMod d₁ => i.val < q)) =
              Finset.range q := by
            ext j; simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
            constructor
            · rintro ⟨i, hi, rfl⟩; exact hi
            · intro hj
              exact ⟨(j : ZMod d₁),
                by rwa [ZMod.val_natCast_of_lt (lt_trans hj hq_lt)],
                ZMod.val_natCast_of_lt (lt_trans hj hq_lt)⟩
          rw [this]; exact Finset.card_range q
      · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
        have : (Finset.univ.filter (fun i : ZMod d₁ => i.val = q)).card = 1 := by
          have : Finset.univ.filter (fun i : ZMod d₁ => i.val = q) = {(q : ZMod d₁)} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_singleton]
            constructor
            · intro h; exact ZMod.val_injective _ (by
                rwa [ZMod.val_natCast_of_lt hq_lt])
            · intro h; rw [h, ZMod.val_natCast_of_lt hq_lt]
          rw [this]; exact Finset.card_singleton _
        rw [this, one_mul]
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
  rw [hsplit, Finset.sum_union (by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]; grind),
    Finset.sum_singleton]

/-- When i is the max element, {k | k < i} ∪ {i} = univ. -/
private lemma zmod_filter_sum_last {n : ℕ} [NeZero n] (f : ZMod n → ℕ) (i : ZMod n)
    (hi : i.val = n - 1) :
    (Finset.univ.filter (fun k : ZMod n => k.val < i.val)).sum f + f i =
    Finset.univ.sum f := by
  rw [← zmod_filter_sum_succ f i]; congr 1; ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ => True.intro, fun _ => by have := k.val_lt (n := n); grind⟩

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
  have he1_pos : 0 < e₁ := by grind
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
  -- d₁ is odd, > 1, and ¬(3∣d₁), so d₁ ≥ 5
  have hd1_ge5 : d₁ ≥ 5 := by grind
  obtain ⟨vals, hvals_bound, hvals_sum⟩ := case2d_rotation_sum_exists hd1_ge5 he1_ge he1_odd k₀.val
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
      grind [ZMod.val_lt]
    refine ⟨0, j + k₀, ?_, ?_⟩
    · rw [← hn, hij]; exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    · have hrot0 : rot (0 : ZMod d₁) = 0 := by simp [rot, ZMod.val_zero]
      have htotal : (Finset.univ.filter (fun k : ZMod d₁ => k.val < i.val)).sum vals +
            vals i = Finset.univ.sum vals := zmod_filter_sum_last vals i hi_eq
      rw [hrot0, Nat.add_zero, ZMod.val_add, Nat.mod_mod_of_dvd _ (dvd_refl e₁)]
      exact pos_shift_wrap' j.val _ (vals i) k₀.val e₁ (by rw [htotal, hvals_sum])

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
  -- Coloring: χ(x) = (j + pattern(i)) mod 3 where (i,j) = Φ⁻¹(x)
  let χ : ZMod m → Fin 3 := fun x =>
    let coord := Φ.symm x
    ⟨(coord.2.val + (case2c_pattern d₁ k₀.val coord.1.val).val) % 3,
     Nat.mod_lt _ (by grind)⟩
  refine ⟨χ, fun n k => ?_⟩
  -- χ at orbit coordinates
  have hχ_eq : ∀ (i' : ZMod d₁) (j' : ZMod e₁),
      χ (Φ (i', j')) = ⟨(j'.val + (case2c_pattern d₁ k₀.val i'.val).val) % 3,
        Nat.mod_lt _ (by grind)⟩ := by
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
      rw [intCast_2ba_eq, ← add_assoc, ← hΦ_ba]
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
      grind [ZMod.val_lt]
    set j' : ZMod e₁ := j + k₀
    set p₀ := case2c_pattern d₁ k₀.val 0
    -- Shift: n + (b-a) = Φ(0, j')
    have hΦ_ba : Φ (0, j') = n + ((b - a : ℤ) : ZMod m) := by
      rw [← hn, hij]
      exact (case2d_shift_ba_wrap he1_b_zero k₀ hk₀ i hi_eq j).symm
    -- Shift: n + (2b-a) = Φ(0, j'+1)
    have hΦ_2ba : Φ (0, j' + 1) = n + ((2 * b - a : ℤ) : ZMod m) := by
      rw [intCast_2ba_eq, ← add_assoc, ← hΦ_ba]
      exact (orbitMap_shift_b he1_b_zero (0, j')).symm
    -- Coverage hypothesis: (j + p_last) % 3 ≠ (j + k₀ + p₀) % 3
    have hp_eq : p = case2c_pattern d₁ k₀.val (d₁ - 1) := by
      change case2c_pattern d₁ k₀.val i.val = _; rw [hi_eq]
    have hhyp : (j.val + p.val) % 3 ≠ (j.val + k₀.val + p₀.val) % 3 := by
      rw [hp_eq]; exact case2c_wrap_hyp d₁ k₀.val j.val hd1_ge3 hd1_odd
    -- Apply cover_mod3_general
    rcases cover_mod3_general p p₀ j.val (j.val + k₀.val) hhyp k with h | h | h | h
    · exact ⟨0, zero_mem_zmod_set m a b,
        by rw [add_zero, ← hn, hij, hχ_eq, h]⟩
    · refine ⟨((b : ℤ) : ZMod m), intCast_b_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_b, hχ_eq, h]; congr 1
      rw [hzmod_succ, case2c_mod3 he1_div3]
    · refine ⟨((b - a : ℤ) : ZMod m), intCast_ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_ba, hχ_eq, h]; congr 1
      change (j'.val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 =
        (j.val + k₀.val + p₀.val) % 3
      have hj'val : j'.val = (j.val + k₀.val) % e₁ := ZMod.val_add j k₀
      rw [ZMod.val_zero, hj'val]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) p₀.val
    · refine ⟨((2 * b - a : ℤ) : ZMod m), intCast_2ba_mem_zmod_set m a b, ?_⟩
      rw [← hΦ_2ba, hχ_eq, h]; congr 1
      change ((j' + 1).val + (case2c_pattern d₁ k₀.val (ZMod.val 0)).val) % 3 =
        (j.val + k₀.val + 1 + p₀.val) % 3
      have hj'val : j'.val = (j.val + k₀.val) % e₁ := ZMod.val_add j k₀
      rw [ZMod.val_zero, hzmod_succ, hj'val]
      rw [case2c_mod3 he1_div3 ((j.val + k₀.val) % e₁ + 1) p₀.val,
        Nat.add_assoc ((j.val + k₀.val) % e₁),
        Nat.add_assoc (j.val + k₀.val)]
      exact case2c_mod3 he1_div3 (j.val + k₀.val) (1 + p₀.val)

/-- Auxiliary: rules out both cycle lengths being ≤ 17 when m ≥ 289. -/
private lemma no_both_e_small {m d₁ d₂ : ℕ}
    (hm : m ≥ 289)
    (hcop : Nat.gcd d₁ d₂ = 1)
    (hd₁_gt1 : d₁ > 1) (hd₂_gt1 : d₂ > 1)
    (hd₁_dvd : d₁ ∣ m) (hd₂_dvd : d₂ ∣ m)
    (he₁_le : m / d₁ ≤ 17) (he₂_le : m / d₂ ≤ 17) : False := by
  have hd₁_bound : m ≤ d₁ * 17 := by
    rw [← Nat.mul_div_cancel' hd₁_dvd]; gcongr
  have hd₂_bound : m ≤ d₂ * 17 := by
    rw [← Nat.mul_div_cancel' hd₂_dvd]; gcongr
  have hprod_le : d₁ * d₂ ≤ m :=
    Nat.le_of_dvd (by grind)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by rwa [Nat.Coprime]) hd₁_dvd hd₂_dvd)
  -- d₁*d₂ ≤ m ≤ d₁*17 → d₂ ≤ 17; similarly d₁ ≤ 17
  have hd₂_le : d₂ ≤ 17 := Nat.le_of_mul_le_mul_left (hprod_le.trans hd₁_bound) (by grind)
  have hd₁_le : d₁ ≤ 17 :=
    Nat.le_of_mul_le_mul_left (mul_comm d₁ d₂ ▸ hprod_le.trans hd₂_bound) (by grind)
  -- 289 ≤ m ≤ d₁*17 → d₁ ≥ 17; similarly d₂ ≥ 17
  -- So d₁ = d₂ = 17, gcd(17,17) = 17 ≠ 1.
  have hd₁_eq : d₁ = 17 := by grind
  have hd₂_eq : d₂ = 17 := by grind
  rw [hd₁_eq, hd₂_eq] at hcop; simp at hcop

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
            change (b - a - -a).natAbs = b.natAbs; congr 1; ring
          have hcop' : (Nat.gcd b'.natAbs m).gcd (Nat.gcd (b' - a').natAbs m) = 1 := by
            rw [hba_eq]; rwa [Nat.gcd_comm]
          have hmin' : min (Nat.gcd b'.natAbs m) (Nat.gcd (b' - a').natAbs m) > 1 := by
            rw [hba_eq]; rwa [min_comm]
          have h3' : ¬ (3 ∣ Nat.gcd b'.natAbs m) := by
            intro h3d'; have := Nat.dvd_gcd h3 h3d'
            rw [h_gcd_coprime] at this
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
      have hd₂_pos : 0 < d₂ := Nat.pos_of_ne_zero (by intro h; simp [h] at hmin)
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
            change (b' - a' - -a').natAbs = b'.natAbs; congr 1; ring
          have hcop' : (Nat.gcd b''.natAbs m).gcd (Nat.gcd (b'' - a'').natAbs m) = 1 := by
            rw [hba_eq]; rwa [Nat.gcd_comm]
          have hmin' : min (Nat.gcd b''.natAbs m) (Nat.gcd (b'' - a'').natAbs m) > 1 := by
            rw [hba_eq]; rwa [min_comm]
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

/-! ## Assembly: connecting ZMod m back to ℤ

The remaining lemmas are the glue between the Case 1/Case 2 analysis in $\mathbb{Z}_m$
and the final statement over $\mathbb{Z}$, culminating in `normal_bit`.
-/

section Assembly

/-- Auxiliary: the set zmod_set m a b has 4 elements when 0 < a < b and 2b - a < m. -/
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

/-- Auxiliary: the coprimality gcd(d₁, d₂) = 1 follows from gcd(a, b, c) = 1. -/
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
  have hd_a : (d : ℤ) ∣ a := by
    have : a = b - (b - a) := by ring
    rw [this]
    exact dvd_sub hd_b hd_ba
  have hd_c : (d : ℤ) ∣ c := by
    have : (c : ℤ) = ↑m - b + a := by grind
    rw [this]
    exact dvd_add (dvd_sub hd_m hd_b) hd_a
  have hd_dvd_gcd : (d : ℤ) ∣ Finset.gcd {a, b, c} id :=
    Finset.dvd_gcd (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hd_a
      · exact hd_b
      · exact hd_c)
  rw [hgcd] at hd_dvd_gcd
  exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp hd_dvd_gcd)

/-- Auxiliary: lifts polychromaticity from ZMod m back to ℤ, combining the
    homomorphism ℤ → ZMod m (Lemma 12(ii)) with `polychromNumber_zmod`. -/
lemma hasPolychromColouring_of_zmod_set {a b c : ℤ} {m : ℕ}
    (hm_eq : (m : ℤ) = c - a + b)
    (h : HasPolychromColouring (Fin 3) (zmod_set m a b)) :
    HasPolychromColouring (Fin 3) ({0, a, b, c} : Finset ℤ) := by
  apply HasPolychromColouring.of_image (Int.castAddHom (ZMod m))
  change HasPolychromColouring (Fin 3) (({0, a, b, c} : Finset ℤ).image (Int.cast : ℤ → ZMod m))
  apply hasPolychromColouring_fin_of_le (by simp)
  rw [polychromNumber_zmod hm_eq]
  exact le_polychromNumber h

/--
**Main theorem of this file.** Every 4-element set $\{0, a, b, c\}$ satisfying the
normalization conditions ($0 < a < b$, $a + b \le c$, $c \ge 289$, $\gcd(a, b, c) = 1$)
admits a 3-polychromatic coloring.

This is the entry point used by `Main.lean` to handle the large-c case. The proof
dispatches to `main_case_one` or `main_case_two` based on
$\min(\gcd(b, m), \gcd(b{-}a, m))$.
-/
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

end Assembly
