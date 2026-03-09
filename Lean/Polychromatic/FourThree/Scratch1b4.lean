import Polychromatic.Colouring
import Polychromatic.PolychromNumber
import Polychromatic.ForMathlib.Misc

/-!
# Coverage proof for `case_one_interval` (Combi.lean:687–763)

## What this file is

A scratch file for developing the proof of `coverage_assembly`, the last
sorry in `case_one_interval` (Combi.lean:763). Once `coverage_assembly` is
proven here, the proof gets integrated into Combi.lean and this file is
deleted.

## What to do

**One task remains**: prove `coverage_assembly` (currently `sorry`).

All helper lemmas it depends on are proven in this file. The proof plan
is documented in the docstring immediately above `coverage_assembly`.

## How to verify

From the `Lean/` directory:

```
lake exe cache get                                    # first time only
lake env lean Polychromatic/FourThree/Scratch1b4.lean # check this file
```

**Success** = only `sorry` warnings from the STUBS section and from
`coverage_assembly` itself. No errors. The stubs are sorry'd duplicates
of lemmas already proven in Combi.lean — they exist only so this file
type-checks independently.

After proving `coverage_assembly`, the only remaining sorry warnings
should be from the STUBS section (lines marked with the ╔══STUBS══╗
banner).

## How to integrate into Combi.lean

After `coverage_assembly` compiles without sorry:

1. **Move to Combi.lean** (all 7 lemmas, near existing `eqp_*` lemmas):
   - `vg_mod_shift` — pure arithmetic, no deps on other helpers
   - `gap2_jg_mod3` — pure arithmetic, no deps
   - `gap1_j0_mod3` — pure arithmetic, no deps
   - `eqp_idx_succ_lt_m` — uses `eqp_idx_m` (already in Combi.lean)
   - `non_straddle_witness` — uses `eqp_off_succ_same`, `compl_parity_witness`
   - `straddle_boundary_color` — uses `eqp_off_succ_new`, `eqp_idx_m`
   - `coverage_assembly` — uses all 6 above + `two_pairs_cover_split`,
     `eqp_idx_step`, `straddle1_gap2`, `straddle2_gap1` (all in Combi.lean)
2. **Do NOT move**: the stubs (already in Combi.lean) or the
   Verification section (test-only code).
3. At Combi.lean:763 (the sorry in `case_one_interval`), call
   `coverage_assembly` with `rfl` for `hq`/`hr`/`hj₀_def`/`hjg_def` and
   `idx_in_interval'` for the interval bounds.
   The `case_one_interval_test` at the bottom of this file shows exactly
   how to wire the arguments.
4. Verify: `lake env lean Polychromatic/FourThree/Combi.lean`
5. Delete this file.

## Do not touch

- **STUBS section**: sorry'd duplicates of Combi.lean lemmas. Do not prove
  these — they already exist in Combi.lean.
- **Verification section** (bottom of file): integration test showing
  `coverage_assembly` fills the sorry. Do not modify.
- **Helper lemmas** (eqp_idx_succ_lt_m through gap1_j0_mod3): all proven,
  do not modify unless `coverage_assembly` needs a different interface.

## Context

The main theorem (`Main.lean:final_result`) proves every 4-element integer
set admits a 3-polychromatic colouring. After reductions:

```
final_result
 ├─ c < 289: computational (done)
 └─ c ≥ 289: combinatorial
     ├─ Case 1: ∃ s with 3∣s, g in middle range
     │   ├─ Case 1a: done
     │   └─ Case 1b: case_one_interval ← THIS sorry
     └─ Case 2: done
```

`case_one_interval` constructs a 3-colouring of `ZMod m` that is
`{0, 1, g, g+1}`-polychromatic. The colouring partitions `[0, m)` into
`s` near-equal intervals and assigns colour `(idx(p) + off(p) % 2) % 3`.
The sorry at line 763 asks for:
```
∃ a ∈ {0, 1, g, g+1}, c(v + a) = k.val
```

## Key definitions

- `q = m / s`, `r = m % s`, so `m = s * q + r` with `r < s`
- `bd = r * (q + 1)` — boundary between long and short intervals
- `eqp_idx q r p` = interval index of position `p`
  (defeq to `let idx` in Combi.lean)
- `eqp_off q r p` = offset within interval
  (defeq to `let off` in Combi.lean)
- `equiEndpoint m s j` = start of interval `j`
-/

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║ STUBS: already proven in Combi.lean (sorry here = placeholder) ║
-- ╚══════════════════════════════════════════════════════════════════╝

private def eqp_idx (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p / (q + 1)
  else r + (p - r * (q + 1)) / q

private def eqp_off (q r : ℕ) (p : ℕ) : ℕ :=
  if p < r * (q + 1) then p % (q + 1)
  else (p - r * (q + 1)) % q

private lemma eqp_idx_step (q r p : ℕ) (hq : 0 < q) :
    eqp_idx q r (p + 1) = eqp_idx q r p ∨
    eqp_idx q r (p + 1) = eqp_idx q r p + 1 := by sorry

private lemma eqp_idx_m (q r s : ℕ) (hq : 0 < q) (hr : r < s)
    (_hs : 0 < s) :
    eqp_idx q r (s * q + r) = s := by sorry

private lemma eqp_off_succ_same (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p) :
    eqp_off q r (p + 1) = eqp_off q r p + 1 := by sorry

private lemma eqp_off_succ_new (q r p : ℕ) (hq : 0 < q)
    (h : eqp_idx q r (p + 1) = eqp_idx q r p + 1) :
    eqp_off q r (p + 1) = 0 := by sorry

private lemma compl_parity_witness (j a : ℕ) (t : ℕ)
    (ht : t < 3)
    (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    (j + a % 2) % 3 = t ∨ (j + (a + 1) % 2) % 3 = t := by sorry

private lemma two_pairs_cover_split (j₁ j₂ : ℕ)
    (hne : j₁ % 3 ≠ j₂ % 3)
    (t : ℕ) (ht : t < 3) :
    (t = j₁ % 3 ∨ t = (j₁ + 1) % 3) ∨
    (t = j₂ % 3 ∨ t = (j₂ + 1) % 3) := by sorry

open Finpartition in
private lemma straddle1_gap2 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (q : ℕ) (hq : q = m / s)
    (r : ℕ) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (v : ℕ) (hv : v < m)
    (j₀ jg : ℕ)
    (hj₀ : j₀ = eqp_idx q r v) (hjg : jg = eqp_idx q r ((v + g) % m))
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hstrad : eqp_idx q r (v + 1) = eqp_idx q r v + 1)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 2 := by sorry

open Finpartition in
private lemma straddle2_gap1 (s g m : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (q : ℕ) (hq : q = m / s)
    (r : ℕ) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (v : ℕ) (hv : v < m)
    (j₀ jg : ℕ)
    (hj₀ : j₀ = eqp_idx q r v) (hjg : jg = eqp_idx q r ((v + g) % m))
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hstrad : eqp_idx q r (((v + g) % m) + 1) =
      eqp_idx q r ((v + g) % m) + 1)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1))
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2) :
    (jg + s - j₀) % s = 1 := by sorry

-- ╔══════════════════════════════════════════════════════════════════╗
-- ║ NEW WORK: helpers + assembly that need real proofs             ║
-- ╚══════════════════════════════════════════════════════════════════╝

/-! ### Proof plan for `coverage_assembly`

**Goal**: Given color `k : Fin 3`, find `a ∈ {0, 1, g, g+1}` such that
`(eqp_idx q r ((v+a) % m) + eqp_off q r ((v+a) % m) % 2) % 3 = k`.

Write `F(p) = (eqp_idx q r (p%m) + eqp_off q r (p%m) % 2) % 3` for the
coloring function. We have two "pairs":
- Pair 1: positions `v` and `v+1` (offsets a=0, a=1)
- Pair 2: positions `v+g` and `v+g+1` (offsets a=g, a=g+1)

Each pair `{p, p+1}` lies in interval `j` or straddles `j/(j+1)`:
- **Non-straddling** (eqp_idx(p+1) = eqp_idx(p)):
  Consecutive offsets have different parities, so `{F(p), F(p+1)} = {j%3, (j+1)%3}`.
  → `non_straddle_witness` gives the right offset d ∈ {0,1}.
- **Straddling** (eqp_idx(p+1) = eqp_idx(p) + 1):
  `eqp_off(p+1) = 0`, so `F(p+1) = (j+1) % 3`.
  → `straddle_boundary_color` handles both p+1 < m and p+1 = m.

**Step 1** (`two_pairs_cover_split`): Since `j₀ % 3 ≠ jg % 3`,
every `k < 3` is in `{j₀%3, (j₀+1)%3}` or `{jg%3, (jg+1)%3}`.

**Step 2** (`eqp_idx_step`): For each pair, case split straddle vs non-straddle.

**Step 3** (Non-straddle cases):
- Pair 1 non-straddle: `non_straddle_witness` → d ∈ {0,1} → a = d.
- Pair 2 non-straddle: `non_straddle_witness` → d ∈ {0,1} → a = g + d.
  Use `vg_mod_shift` to rewrite `(v+(g+d)) % m = ((v+g)%m + d) % m`.

**Step 4** (Straddle cases — use the OTHER pair):
- Pair 1 straddles → `straddle1_gap2` → gap = 2 → `gap2_jg_mod3`:
  `(jg+1)%3 = j₀%3`.
  - If k = (j₀+1)%3: witness a=1 via `straddle_boundary_color`.
  - If k = j₀%3 = (jg+1)%3: pair 2 can't straddle (would force gap=1,
    contradicting gap=2). Use `non_straddle_witness` on pair 2.
- Pair 2 straddles → `straddle2_gap1` → gap = 1 → `gap1_j0_mod3`:
  `(j₀+1)%3 = jg%3`. Symmetric.

Both pairs straddling is impossible (gap can't be both 1 and 2).

### Witness summary

| Pair 1     | Pair 2     | Target           | Witness |
|------------|------------|------------------|---------|
| non-strad  | —          | in {j₀, j₀+1}%3 | a = d   |
| —          | non-strad  | in {jg, jg+1}%3  | a = g+d |
| straddle   | non-strad  | (j₀+1)%3        | a = 1   |
| straddle   | non-strad  | j₀%3 = (jg+1)%3 | a = g+d |
| non-strad  | straddle   | (jg+1)%3        | a = g+1 |
| non-strad  | straddle   | jg%3 = (j₀+1)%3 | a = d   |
-/
/-! #### Helper 1: p+1 < m when eqp_idx doesn't jump to s -/
private lemma eqp_idx_succ_lt_m (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s) (hs : 0 < s)
    (hm_eq : m = s * q + r)
    (hp : p < m) (hidx_lt : eqp_idx q r p < s) :
    p + 1 < m ∨ eqp_idx q r (p + 1) = s := by
  by_cases h : p + 1 < m
  · exact Or.inl h
  · have hpm : p + 1 = m := by omega
    right
    rw [hpm, hm_eq]
    exact eqp_idx_m q r s hq_pos hr_lt hs

/-! #### Helper 2: non-straddle witness

If eqp_idx doesn't step at p, and target k is in {j%3, (j+1)%3},
produce d ∈ {0,1} with the coloring formula at (p+d)%m equaling k. -/
private lemma non_straddle_witness (q r p : ℕ)
    (hq_pos : 0 < q)
    (hp : p < m) (hp1 : p + 1 < m)
    (hsame : eqp_idx q r (p + 1) = eqp_idx q r p)
    (j : ℕ) (hj : j = eqp_idx q r p)
    (t : ℕ) (ht : t < 3) (hpair : t = j % 3 ∨ t = (j + 1) % 3) :
    ∃ d ∈ ({0, 1} : Finset ℕ),
      (eqp_idx q r ((p + d) % m) +
        eqp_off q r ((p + d) % m) % 2) % 3 = t := by
  have hoff := eqp_off_succ_same q r p hq_pos hsame
  rcases compl_parity_witness j (eqp_off q r p) t ht hpair with h | h
  · exact ⟨0, by simp, by
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hp, ← hj]
      exact h⟩
  · exact ⟨1, by simp, by
      rw [Nat.mod_eq_of_lt hp1, hsame, ← hj, hoff]
      exact h⟩

/-! #### Helper 3: straddle boundary color

When eqp_idx steps at p, the coloring at p+1 gives (j+1)%3,
handling the edge case p+1 = m (wraps to 0). -/
private lemma straddle_boundary_color (q r s p : ℕ)
    (hq_pos : 0 < q) (hr_lt : r < s) (hs : 0 < s)
    (hs3 : 3 ∣ s)
    (hm_eq : m = s * q + r)
    (hp : p < m)
    (hstep : eqp_idx q r (p + 1) = eqp_idx q r p + 1)
    (j : ℕ) (hj : j = eqp_idx q r p) (hj_lt : j < s) :
    (eqp_idx q r ((p + 1) % m) +
      eqp_off q r ((p + 1) % m) % 2) % 3 = (j + 1) % 3 := by
  by_cases h : p + 1 < m
  · -- Normal case: p + 1 < m
    rw [Nat.mod_eq_of_lt h]
    have hoff := eqp_off_succ_new q r p hq_pos hstep
    rw [hstep, ← hj, hoff]
  · -- Wrap case: p + 1 = m
    have hpm : p + 1 = m := by omega
    rw [hpm, Nat.mod_self]
    have hidx0 : eqp_idx q r 0 = 0 := by
      simp [eqp_idx]
    have hoff0 : eqp_off q r 0 = 0 := by
      simp [eqp_off]
    rw [hidx0, hoff0]
    -- Need: 0 = (j + 1) % 3. Since eqp_idx(m) = s = j+1 and 3 | s.
    rw [hpm] at hstep
    have hm_idx : eqp_idx q r m = s := by
      rw [hm_eq]; exact eqp_idx_m q r s hq_pos hr_lt hs
    have hjs : j + 1 = s := by rw [hj]; omega
    obtain ⟨d3, hd3⟩ := hs3; omega

/-! #### Helper 4: modular shift for vg

`(v + (g + d)) % m = ((v + g) % m + d) % m` -/
private lemma vg_mod_shift (v g d : ℕ) (hm : 0 < m) :
    (v + (g + d)) % m = ((v + g) % m + d) % m := by
  have h1 := Nat.add_mod (v + g) d m
  have h2 := Nat.add_mod ((v + g) % m) d m
  rw [Nat.mod_mod_of_dvd _ (dvd_refl m)] at h2
  rw [show v + (g + d) = (v + g) + d from by ring, h1, h2]

/-! #### Helper 5: gap=2 implies (jg+1)%3 = j₀%3 -/
private lemma gap2_jg_mod3 (s j₀ jg : ℕ) (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap2 : (jg + s - j₀) % s = 2) :
    (jg + 1) % 3 = j₀ % 3 := by
  obtain ⟨d3, hd3⟩ := hs3
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  have : (jg + s - j₀) / s ≤ 1 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < s)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h
  · rw [h] at hdiv; omega
  · have : (jg + s - j₀) / s = 1 := by omega
    rw [this] at hdiv; omega

/-! #### Helper 6: gap=1 implies (j₀+1)%3 = jg%3 -/
private lemma gap1_j0_mod3 (s j₀ jg : ℕ) (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap1 : (jg + s - j₀) % s = 1) :
    (j₀ + 1) % 3 = jg % 3 := by
  obtain ⟨d3, hd3⟩ := hs3
  have hdiv := Nat.div_add_mod (jg + s - j₀) s
  have : (jg + s - j₀) / s ≤ 1 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < s)]; omega
  rcases Nat.eq_zero_or_pos ((jg + s - j₀) / s) with h | h
  · rw [h] at hdiv; omega
  · have : (jg + s - j₀) / s = 1 := by omega
    rw [this] at hdiv; omega

/-! #### Main assembly -/
open Finpartition in
private lemma coverage_assembly (s g m q r : ℕ)
    (hs : 0 < s) (hs3 : 3 ∣ s) (hs3_le : 3 ≤ s) (hs_le : s ≤ m)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s))
    (hg1_lt_m : g + 1 < m)
    (hq : q = m / s) (hr : r = m % s)
    (hq_pos : 0 < q) (hr_lt : r < s)
    (hm_eq : m = s * q + r)
    (v : ℕ) (hv : v < m) (k : Fin 3)
    (j₀ : ℕ) (hj₀_def : j₀ = eqp_idx q r v)
    (jg : ℕ) (hjg_def : jg = eqp_idx q r ((v + g) % m))
    (hphase : j₀ % 3 ≠ jg % 3)
    (hgap : (jg + s - j₀) % s = 1 ∨ (jg + s - j₀) % s = 2)
    (hj₀_lt : j₀ < s) (hjg_lt : jg < s)
    (hv_lo : equiEndpoint m s j₀ ≤ v)
    (hv_hi : v < equiEndpoint m s (j₀ + 1))
    (hvg_lo : equiEndpoint m s jg ≤ (v + g) % m)
    (hvg_hi : (v + g) % m < equiEndpoint m s (jg + 1)) :
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      (eqp_idx q r ((v + a) % m) +
        eqp_off q r ((v + a) % m) % 2) % 3 = k.val := by
  sorry

/-! ### Verification: check coverage_assembly fills the sorry in case_one_interval

We copy `case_one_interval` with sorry'd stubs for its private dependencies,
and verify that `coverage_assembly` (also sorry'd) can close the goal. -/
section Verification

-- Stubs for private lemmas from Combi.lean
private lemma lift_coloring_witness_stub {m g : ℕ} [NeZero m]
    [Fact (1 < m)] (hg_lt : g + 1 < m)
    {c : ℕ → ℕ} (hc_lt : ∀ p, c p < 3)
    (hc_period : ∀ p, c (p % m) = c p)
    {n : ZMod m} {k : Fin 3}
    (h : ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ),
      c (n.val + a) = k.val) :
    ∃ s ∈ ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
      Finset (ZMod m)),
      (⟨c (n + s).val, hc_lt _⟩ : Fin 3) = k := by sorry

private lemma gap_bound_interval_stub (s g m : ℕ) (hs : 0 < s)
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
  sorry

private lemma phase_ne_of_gap_stub {s j₀ jg : ℕ} (hs3 : 3 ∣ s)
    (hj₀ : j₀ < s) (hjg : jg < s)
    (hgap : (jg + s - j₀) % s = 1 ∨
      (jg + s - j₀) % s = 2) :
    j₀ % 3 ≠ jg % 3 := by sorry

open Finpartition in
private lemma idx_in_interval_stub (s m : ℕ)
    (hs : 0 < s) (hs_le : s ≤ m) (p : ℕ) (hp : p < m) :
    let q := m / s
    let r := m % s
    let bd := r * (q + 1)
    let j := if p < bd then p / (q + 1)
      else r + (p - bd) / q
    j < s ∧ equiEndpoint m s j ≤ p ∧
    p < equiEndpoint m s (j + 1) := by sorry

-- Full copy of case_one_interval with the sorry replaced by
-- coverage_assembly application
open Finpartition in
private lemma case_one_interval_test (m : ℕ)
    (s g : ℕ) (hs : 0 < s) (hs3 : 3 ∣ s)
    (h_lb : (m + s - 1) / s < g) (h_ub : g < 2 * (m / s)) :
    HasPolychromColouring (Fin 3)
      ({0, 1, (g : ZMod m), (g : ZMod m) + 1} :
        Finset (ZMod m)) := by
  set q := m / s
  set r := m % s
  have hm_eq : m = s * q + r := (Nat.div_add_mod m s).symm
  have hr_lt : r < s := Nat.mod_lt m hs
  have hq_pos : 0 < q := by
    have : q * s ≤ m := Nat.div_mul_le_self m s
    have : q ≤ (m + s - 1) / s := by
      rw [Nat.le_div_iff_mul_le hs]; omega
    omega
  have hs_le : s ≤ m := by
    nlinarith [Nat.div_mul_le_self m s]
  have hg1_lt_m : g + 1 < m := by
    nlinarith [Nat.div_mul_le_self m s, Nat.le_of_dvd hs hs3]
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  set bd := r * (q + 1)
  let idx (p : ℕ) : ℕ :=
    if p < bd then p / (q + 1) else r + (p - bd) / q
  let off (p : ℕ) : ℕ :=
    if p < bd then p % (q + 1) else (p - bd) % q
  let c (p : ℕ) : ℕ :=
    (idx (p % m) + off (p % m) % 2) % 3
  have hc_lt3 : ∀ p, c p < 3 :=
    fun p => Nat.mod_lt _ (by omega)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p; simp only [c]
    rw [Nat.mod_mod_of_dvd p (dvd_refl m)]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness_stub hg1_lt_m hc_lt3 hc_period ?_⟩
  set v := n.val
  have hv_lt : v < m := ZMod.val_lt n
  have hc_phase : ∀ p, c p = idx (p % m) % 3 ∨
      c p = (idx (p % m) + 1) % 3 := by
    intro p; simp only [c]
    have : off (p % m) % 2 = 0 ∨ off (p % m) % 2 = 1 :=
      by omega
    rcases this with h | h <;> simp [h] <;> omega
  set j₀ := idx v with hj₀_def
  set jg := idx ((v + g) % m) with hjg_def
  have hs3_le : 3 ≤ s := Nat.le_of_dvd hs hs3
  have hgap := gap_bound_interval_stub s g m hs hs3_le hs_le
    h_lb h_ub v hv_lt
  have hidx_lt : ∀ p, p < m → idx p < s := by
    intro p hp; simp only [idx]; split
    · have : p / (q + 1) < r := by
        rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1)]
        exact ‹_›
      omega
    · rename_i hge; push_neg at hge
      have : (p - bd) / q < s - r := by
        rw [Nat.div_lt_iff_lt_mul hq_pos]
        have : r * (q + 1) + (s - r) * q = s * q + r := by
          have : (s - r) * q + r * q = s * q := by
            rw [← Nat.add_mul,
              Nat.sub_add_cancel (Nat.le_of_lt hr_lt)]
          linarith
        omega
      omega
  have hj₀_lt : j₀ < s := hidx_lt v hv_lt
  have hjg_lt : jg < s :=
    hidx_lt ((v + g) % m) (Nat.mod_lt _ (by omega))
  have hphase : j₀ % 3 ≠ jg % 3 :=
    phase_ne_of_gap_stub hs3 hj₀_lt hjg_lt hgap
  -- === HERE: the sorry site ===
  -- Goal: ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = k.val
  -- Derive interval membership from idx_in_interval_stub
  have hiv := idx_in_interval_stub s m hs hs_le v hv_lt
  have hivg := idx_in_interval_stub s m hs hs_le
    ((v + g) % m) (Nat.mod_lt _ (by omega))
  -- Bridge: show the goal matches coverage_assembly's conclusion
  have hgoal := coverage_assembly s g m q r
    hs hs3 hs3_le hs_le h_lb h_ub hg1_lt_m
    rfl rfl hq_pos hr_lt hm_eq
    v hv_lt k
    j₀ rfl jg rfl
    hphase hgap hj₀_lt hjg_lt
    hiv.2.1 hiv.2.2 hivg.2.1 hivg.2.2
  exact hgoal

end Verification
