# Plan: Coverage proof for `case_one_interval`

Goal: eliminate the `sorry` at `Combi.lean:763`.

## Context

At the sorry site we have:
- `v < m`, `j₀ = idx(v)`, `jg = idx((v+g)%m)`
- `hphase : j₀ % 3 ≠ jg % 3`
- `hgap : (jg + s - j₀) % s = 1 ∨ ... = 2`
- Local `let` bindings for `c`, `idx`, `off` (not `eqp_idx`/`eqp_off`)
- `hc_phase : ∀ p, c p = idx(p%m) % 3 ∨ c p = (idx(p%m)+1) % 3`

The proof needs: `∃ a ∈ {0, 1, g, g+1}, c(v+a) = k.val`.

## Sub-goals (from Combi.lean TODO comments)

**(a)** Each non-straddling pair `{p, p+1}` in interval `j` gives both
phases `{j%3, (j+1)%3}` (consecutive offsets have different parities).

Depends on: Lemma 4 (`eqp_off_succ_same`) + Lemma 6 (`compl_parity_witness`).

**(b)** A straddling pair always produces `(j+1)%3` (the boundary color).

Depends on: Lemma 5 (`eqp_off_succ_new`) + Lemma 3 (`eqp_idx_step`).
When `idx(p+1) = idx(p) + 1`, `off(p+1) = 0`, so
`c(p+1) = (idx(p)+1 + 0) % 3 = (j+1) % 3`.
Wrap case (`j+1 = s`): `(v+1)%m = 0`, `idx(0) = 0`,
`c(v+1) = 0 = s%3 = (j+1)%3` since `3 ∣ s`.

**(c)** At most one pair straddles (no-double-straddle).

Depends on: Lemma 9 (`straddle1_gap2`) + Lemma 10 (`straddle2_gap1`).
Pair 1 straddles → gap = 2; pair 2 straddles → gap = 1.
These are contradictory, so at most one straddles.

**(d)** When pair 1 straddles at `j₀/(j₀+1)`, pair 2 is entirely in
interval `(j₀+2)%s`, giving `{(j₀+2)%3, j₀%3}`.
(Symmetric statement for pair 2 straddling.)

Depends on: gap value from (c) + sub-goal (a) applied to pair 2.

## Work items

### 1. Easy arithmetic lemmas (no deps)

- [ ] **Lemma 6** (`compl_parity_witness`): `Nat.mod_two_eq_zero_or_one`
  then `omega`.
- [ ] **Lemma 7** (`two_pairs_cover_split`): `omega` after
  `Nat.mod_lt` for both `j₁` and `j₂`.

### 2. General helpers + Lemmas 4, 5

- [ ] **`mod_step`**: `a/b = (a+1)/b → (a+1)%b = a%b + 1`.
  Proof via `Nat.div_add_mod` twice + `omega`.
- [ ] **`mod_zero_step`**: `(a+1)/b = a/b + 1 → (a+1)%b = 0`.
  Proof via `Nat.div_add_mod` twice + `Nat.mod_lt` + `omega`.
- [ ] **Lemma 4** (`eqp_off_succ_same`): `unfold eqp_off; split_ifs`,
  apply `mod_step` in cases 1 and 4, contradiction in case 3.
  Supports **(a)**.
- [ ] **Lemma 5** (`eqp_off_succ_new`): same structure, apply
  `mod_zero_step`. Supports **(b)**.

### 3. Lemma 8

- [ ] **Lemma 8** (`eqp_idx_last`): `idx(m-1) = s-1`.
  `unfold eqp_idx; split_ifs`, show `m-1 ≥ bd`, then division
  identity via `Nat.add_mul_div_right`.

### 4. Straddle lemmas (hardest)

- [ ] **Lemma 9** (`straddle1_gap2`): pair 1 straddle → gap = 2.
  Assume gap = 1, derive contradiction. Two main cases:
  `j₀+1 < s` (non-wrap/wrap) and `j₀ = s-1`.
  Key bounds: `g > ⌈m/s⌉ ≥` interval length, `g < 2q < m`.
  Supports **(c)**.
- [ ] **Lemma 10** (`straddle2_gap1`): pair 2 straddle → gap = 1.
  Assume gap = 2, show circular arc ≥ 2q, contradicting `g < 2q`.
  Supports **(c)**.

### 5. Bridge: connect `eqp_idx`/`eqp_off` to local `let` bindings

The sorry site uses local `let idx`, `let off`, `let c` which are
definitionally equal to `eqp_idx q r`, `eqp_off q r`, and the
coloring formula. Need to show the Scratch1b4 lemmas apply to
these local definitions. Strategy: `show`/`change` or
`have : eqp_idx q r p = idx p := rfl`.

### 6. Assembly at Combi.lean:763

Structure of the final proof:

```
-- By Lemma 7, k is in pair 1's range or pair 2's range
rcases two_pairs_cover_split j₀ jg hphase k.val k.isLt with
  ⟨hk1⟩ | ⟨hk2⟩

-- Case: k ∈ {j₀%3, (j₀+1)%3}
·  by_cases hstrad1 : idx((v+1)%m) = idx(v%m)  -- pair 1 straddles?
   · -- Non-straddling: (a) gives witness
     ...
   · -- Straddling: (b) gives (j₀+1)%3 from c(v+1)
     -- (c) says pair 2 doesn't straddle
     -- (d) + gap=2 means k=j₀%3 is in pair 2's range
     -- (a) on pair 2 gives witness
     ...

-- Case: k ∈ {jg%3, (jg+1)%3}  — symmetric
```

## Execution order

1 → 2 → 3 → 4 → 5 → 6

Items 1, 2, 3 are independent of each other (all go in Scratch1b4.lean).
Item 4 depends on equiEndpoint lemmas from Misc.lean (already proven).
Item 5 is a thin bridge layer.
Item 6 ties everything together at the sorry site.
