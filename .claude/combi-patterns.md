# Combi.lean Proof Patterns

Domain-specific patterns for the proofs in `FourThree/Combi.lean`: block colorings, ZMod arithmetic, and the case structure from the paper.

## Bridge: ℕ coloring → ZMod m polychromatic coloring
Extracted as `lift_coloring_witness` helper. Usage:
```
refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
  lift_coloring_witness (by omega) hc_lt3 hc_period ?_⟩
-- Goal: ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (n.val + a) = k.val
```

## Block coloring arithmetic

### `simp only [c]` does NOT unfold `let` bindings
Use `unfold_let c`, `dsimp only`, or make `c` a local `def` instead of `let`.

### Key mathlib lemmas for block colorings
- `Nat.mul_add_mod h q r : (h * q + r) % h = r % h`
- `Nat.mul_add_div (hh : 0 < h) : (h * q + r) / h = q + r / h`
- `Nat.div_eq_of_lt (hr : r < h) : r / h = 0`
- `Nat.mod_eq_of_lt (hr : r < h) : r % h = r`
- `Nat.mul_mod_right n k : n * k % n = 0`
- `Nat.mul_div_cancel_left _ (hh : 0 < h) : h * q / h = q`
- `Nat.add_mul_div_left r q (hh : 0 < h) : (r + h * q) / h = r / h + q`

### `simp` can't simplify `1 % h = 1` when h is a variable
Use `Nat.mod_eq_of_lt (by omega)` instead.

## ZMod cast patterns

### ℤ→ZMod vs ℕ→ZMod are DIFFERENT cast paths
- `Int.cast b` and `Nat.cast b.natAbs` are different terms even when `b ≥ 0`
- Bridge: `rcases Int.natAbs_eq b with h | h` then `conv_lhs => rw [h]; rw [Int.cast_natCast]`
- `rw [h]` where `h : b = ↑b.natAbs` replaces ALL `b` including inside `b.natAbs` — use `conv_lhs` to restrict

### castHom for coordinate extraction
- `ZMod.castHom (dvd : d₁ ∣ m) (ZMod d₁)` projects ZMod m → ZMod d₁
- `map_intCast`, `map_natCast`, `map_add`, `map_mul` for pushing through
- `nsmul_eq_mul` must be applied BEFORE `map_nsmul` (simp applies bottom-up, so use rw instead)
- Pattern: `rw [nsmul_eq_mul, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]`

### ZMod composite modulus limitations
- No `NoZeroDivisors`, no `IsRightCancelMulZero` for composite `d₁`
- Can't use `mul_right_cancel₀`. Instead: use `IsUnit.mul_right_cancel` or multiply by `↑u⁻¹`
- Unit cancellation: `IsUnit.mul_right_cancel` or `IsUnit.mul_left_eq_zero` work without integral domain

### Fin arithmetic in ZMod proofs
- `hord ▸` (subst-style rewrite) causes kernel errors with `Fin` types — use `rwa [hord] at this`
- `Fin.val_one'` gives `1 % n`, not `1` — need `Nat.mod_eq_of_lt` to simplify when `n ≥ 2`
- `Fin.val_add` gives `(a + b) % n` — may need two `Nat.mod_eq_of_lt` calls

### Useful lemma names
- `Units.mul_inv` (not `Units.val_mul_inv`): `(↑u * ↑u⁻¹ : α) = 1`
- `ZMod.addOrderOf_coe` for addOrderOf of a cast element
- `addOrderOf_dvd_of_nsmul_eq_zero` for extracting divisibility from `n • x = 0`
- `Fintype.bijective_iff_injective_and_card` for finite bijection from injectivity + card match
- `push_cast; ring` closes most pure ZMod algebra goals

## Equiv.ofBijective patterns

- `(Equiv.ofBijective φ hbij) x` is definitionally `φ x`, so hypotheses about `φ` apply to `Φ` without conversion.
- `Φ.symm` uses `Classical.indefiniteDescription` and does NOT reduce — proofs about `Φ.symm` require `Equiv.apply_symm_apply` or `Equiv.symm_apply_eq`.
- When multiple proofs derive properties of `Φ.symm`, extract shared reasoning as private lemmas (e.g. "if `Φ` has a shift property then `Φ⁻¹` has the corresponding inverse-shift property").
- `set` bindings affect definitional equality — `set j := expr` makes goals see `j` instead of `expr`. If you hoist a proof out of its tactic block, `set` bindings are no longer in scope and terms involving `Equiv.symm` may not unify.

## Don't extract tactic blocks that create typeclass instances
`haveI : NeZero m := ⟨by grind⟩` introduces a local instance. Extracting into a helper requires threading instances explicitly, adding more complexity than it removes. Leave these inline.

## Dependent type rewriting

When `rw` fails with "motive is not type correct" because the rewritten term appears in dependent types (e.g. `hab : a ≤ b` depends on `b`), generalize first:

```lean
-- Instead of: rw [hb] which fails
suffices ∀ s, statement_about s by
  convert this _ <;> exact the_equality
intro s
-- prove for arbitrary s (no dependent type issues)
```

This works because the generalized statement has no dependencies on the problematic term, and `convert` handles the coercions at the end.

## mod3_witness dispatch pattern
```
set s := ... with hs_def
have hs_lt : s < 3 := Nat.mod_lt _ (by omega)
rw [hs_def] at hcv
set d := (k.val + 3 - s) % 3
rcases show d = 0 ∨ d = 1 ∨ d = 2 from by omega with hd | hd | hd
```
The witness mapping (which of {0,1,g,g+1} gives color k) varies per case,
so this can't easily be extracted further.
