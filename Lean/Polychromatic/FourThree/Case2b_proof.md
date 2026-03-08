# Informal Proof of Case 2b: d₁ even, e₁ odd

## Setup

We work in ZMod m with m ≥ 289. Let d₁ = gcd(b, m) and e₁ = m/d₁. We assume:
- gcd(d₁, d₂) = 1 where d₂ = gcd(b−a, m)
- min(d₁, d₂) > 1 (multiple cycles)
- d₁ is even
- e₁ is odd

The group ZMod m decomposes into d₁ cycles of length e₁:
  C_i = {i(b−a) + jb mod m : 0 ≤ j < e₁}

Any translate of S = {0, b−a, b, 2b−a} takes the form
  {c_{i,j}, c_{i,j+1}, c_{i+1,j'}, c_{i+1,j'+1}}
where subscripts are mod d₁ and mod e₁ respectively.

Since d₁ is even, cycles come in consecutive pairs (C₀,C₁), (C₂,C₃), ..., (C_{d₁−2},C_{d₁−1}).

## Coloring

Define the coloring χ: ZMod m → Fin 3 via the product decomposition φ: ZMod d₁ × ZMod e₁ ≅ ZMod m.

For each pair of cycles:
- **Even cycle C_{2i}**: color position j by the pattern `01010...011`
  - Formula: f(j) = if j = e₁−1 then 1 else j mod 2
  - This alternates 0,1,0,1,...,0,1 for j = 0,...,e₁−2, then ends with an extra 1 at j = e₁−1.
  - Since e₁ is odd, the "normal" alternation would end at j = e₁−2 (odd index) with color 1, and position e₁−1 (even index) would get 0. We override this to 1.

- **Odd cycle C_{2i+1}**: color position j by the pattern `22020...020`
  - Formula: f(j) = if j = 0 then 2 else if j is even then 0 else 2
  - Position 0 gets color 2. Then for j ≥ 1: odd positions get 2, even positions get 0.
  - Since e₁ is odd, the last position e₁−1 is even, so it gets 0. The pattern reads 2,2,0,2,0,...,2,0.
  - Wait — position 1 is odd → 2. So positions 0,1 are both 2. Then position 2 is even → 0, position 3 is odd → 2, etc. Pattern: 2,2,0,2,0,2,0,...,2,0.

## Lemma 1: Even cycles use only colors {0, 1}

**Statement**: For any even cycle index i (i.val % 2 = 0) and any position j, the color f(i,j) is either 0 or 1.

**Proof**: If j = e₁−1, the color is 1. Otherwise, the color is j mod 2, which is either 0 or 1. In no case is the color 2. ∎

## Lemma 2: Odd cycles use only colors {0, 2}

**Statement**: For any odd cycle index i (i.val % 2 = 1) and any position j, the color f(i,j) is either 0 or 2.

**Proof**: If j = 0, the color is 2. If j ≥ 1 and j is even, the color is 0. If j ≥ 1 and j is odd, the color is 2. In no case is the color 1. ∎

## Lemma 3: Every consecutive pair on an even cycle contains color 1

**Statement**: For any even cycle index i and any position j:
  f(i,j) = 1 ∨ f(i,j+1) = 1

**Proof**: Consider cases on j (working modulo e₁):
- If j = e₁−1: f(i,j) = 1. Done.
- If j < e₁−1 and j is odd: f(i,j) = j mod 2 = 1. Done.
- If j < e₁−1 and j is even: Then j+1 is odd and j+1 ≤ e₁−1. If j+1 < e₁−1, f(i,j+1) = (j+1) mod 2 = 1. If j+1 = e₁−1, f(i,j+1) = 1. Either way, f(i,j+1) = 1. Done. ∎

## Lemma 4: Every consecutive pair on an odd cycle contains color 2

**Statement**: For any odd cycle index i and any position j:
  f(i,j) = 2 ∨ f(i,j+1) = 2

**Proof**: Consider cases on j (working modulo e₁):
- If j = 0: f(i,j) = 2. Done.
- If j ≥ 1 and j is odd: f(i,j) = 2. Done.
- If j ≥ 1 and j is even: Then j ≠ 0, so f(i,j) = 0. We need f(i,j+1) = 2. Since j is even, j+1 is odd. If j+1 < e₁ (i.e., j < e₁−1): since j+1 ≥ 1 and j+1 is odd, f(i,j+1) = 2. If j = e₁−1 (i.e., j+1 wraps to 0): f(i,0) = 2. Either way, f(i,j+1) = 2. Done. ∎

## Lemma 5: The even-cycle consecutive pair {1,1} occurs only at j = e₁−2

**Statement**: If f(i,j) = 1 and f(i,j+1) = 1 for an even cycle, then j.val = e₁−2.

**Proof**: We need both f(i,j) = 1 and f(i,j+1) = 1.
- f(i,j) = 1 means either j = e₁−1 or (j < e₁−1 and j is odd).
- f(i,j+1) = 1 means either j+1 = e₁−1 (mod e₁) or (j+1 < e₁−1 and j+1 is odd).

Case j = e₁−1: Then j+1 ≡ 0 (mod e₁), so (j+1).val = 0. f(i, pos 0) = 0 mod 2 = 0 (since 0 ≠ e₁−1 when e₁ ≥ 3). So f(i,j+1) = 0 ≠ 1. Contradiction.

Case j < e₁−1 and j odd: f(i,j) = 1 ✓. For f(i,j+1) = 1: Since j is odd, j+1 is even. If j+1 < e₁−1, then f(i,j+1) = (j+1) mod 2 = 0 ≠ 1. So we need j+1 = e₁−1, i.e., j = e₁−2. ∎

## Lemma 6: The odd-cycle consecutive pair {2,2} occurs only at j = 0

**Statement**: If f(i,j) = 2 and f(i,j+1) = 2 for an odd cycle, then j.val = 0.

**Proof**: We need both f(i,j) = 2 and f(i,j+1) = 2.
- f(i,j) = 2 means either j = 0 or (j ≥ 1 and j is odd).
- f(i,j+1) = 2 means either (j+1).val = 0 or ((j+1).val ≥ 1 and (j+1).val is odd).

Case j = 0: Done, j.val = 0. ✓

Case j ≥ 1 and j odd: f(i,j) = 2 ✓. For f(i,j+1) = 2: j+1 is even. If (j+1).val = 0 (i.e., j = e₁−1): but j is odd and e₁−1 is even (since e₁ is odd), so j ≠ e₁−1. If (j+1).val ≥ 1: since j+1 is even, we need j+1 odd for color 2, contradiction. So f(i,j+1) ≠ 2. Contradiction with the assumption. ∎

## Lemma 7: e₁ ≥ 3

**Statement**: Under our hypotheses, e₁ ≥ 3.

**Proof**: e₁ is odd, so e₁ ∈ {1, 3, 5, ...}. We rule out e₁ = 1.
If e₁ = 1, then m = d₁ · 1 = d₁, so d₁ = m. Then d₂ = gcd(b−a, m) divides m = d₁. Since gcd(d₁, d₂) = 1 and d₂ | d₁, we get d₂ = 1, contradicting min(d₁, d₂) > 1. ∎

## Lemma 8: The degenerate positions are distinct

**Statement**: When e₁ ≥ 3, we have e₁ − 2 ≠ 0 (as natural numbers, or equivalently as elements of ZMod e₁).

**Proof**: Immediate from e₁ ≥ 3. ∎

## Lemma 9: Coverage — every 2×2 block contains all 3 colors

**Statement**: For any cycle index i, positions j₁, j₂, and target color k ∈ Fin 3:
  k ∈ {f(i,j₁), f(i,j₁+1), f(i+1,j₂), f(i+1,j₂+1)}

**Proof**: Since d₁ is even, i and i+1 have different parities. One of the rows (i, i+1) is even, the other is odd. We prove each color k ∈ {0, 1, 2} appears:

**k = 1**: The even-cycle row (either i or i+1) contains color 1 in its consecutive pair, by Lemma 3.

**k = 2**: The odd-cycle row contains color 2 in its consecutive pair, by Lemma 4.

**k = 0**: Suppose for contradiction that 0 does not appear in any of the 4 positions. Then:
- The even-cycle pair contains no 0. By Lemma 1, its colors are from {0,1}, so both must be 1: the pair is {1,1}.
- The odd-cycle pair contains no 0. By Lemma 2, its colors are from {0,2}, so both must be 2: the pair is {2,2}.
- By Lemma 5, the even pair {1,1} forces j = e₁−2 (in the position of the even row).
- By Lemma 6, the odd pair {2,2} forces j = 0 (in the position of the odd row).
- But j₁ and j₂ can be different! Wait — actually, in the translate structure, the j-coordinates of the two rows ARE potentially different. Let me reconsider.

Actually, looking at the translate structure more carefully: a translate of S is {c_{i,j}, c_{i,j+1}, c_{i+1,j'}, c_{i+1,j'+1}} where j' is NOT necessarily equal to j. In the Case 2a proof, the coverage lemma takes independent j₁ and j₂.

So the argument above doesn't directly work — we need j₁ = e₁−2 AND j₂ = 0 to fail simultaneously, but since j₁ and j₂ are independent, they CAN be these values simultaneously!

**Revised proof for k = 0**: We need a different argument. Let me reconsider...

Actually wait — if the even pair at j₁ is {1,1} and the odd pair at j₂ is {2,2}, then 0 is indeed absent from all 4 positions. The translate would see only colors 1 and 2. This would mean the coloring is NOT polychromatic!

Let me recheck the paper's coloring for Case 2b more carefully.

Looking at the paper: "color each C_{2i} by 01010...011 and each C_{2i+1} by 22020...02"

For e₁ = 3:
- Even: 0,1,1
- Odd: 2,2,0

Consider the translate with i even, j₁ = 1 (even row positions 1,2): colors 1,1. j₂ = 0 (odd row positions 0,1): colors 2,2. The 2×2 block is {1,1,2,2} — only colors 1 and 2! Color 0 is missing!

Hmm, but wait. In the actual translate structure, j₁ and j₂ are NOT independent. Let me re-examine.

The translate of S by n gives {n, n+b, n+(b-a), n+(2b-a)}. Under the bijection φ(i,j) = i(b-a) + jb, if n = φ(i,j) = c_{i,j}, then:
- n + b = c_{i,j+1}
- n + (b-a) = c_{i+1,j} (shifting i by 1 but keeping j the same!)
- n + (2b-a) = c_{i+1,j+1}

So j IS the same for both rows! The translate is {c_{i,j}, c_{i,j+1}, c_{i+1,j}, c_{i+1,j+1}} with the SAME j.

Wait, but Case 2a's coverage lemma uses independent j₁ and j₂. Let me re-read it...

Looking at Case 2a (lines 1070-1071):
```lean
set j' := (Φ.symm (n + ↑(b - a))).2
```
And then the translate is {f(i,j), f(i,j+1), f(i+1,j'), f(i+1,j'+1)}.

So j' is the second coordinate of Φ.symm(n + (b-a)), which is NOT necessarily j! The bijection φ(i,j) = i*(b-a) + j*b maps (i+1, j) to (i+1)*(b-a) + j*b = i*(b-a) + j*b + (b-a) = φ(i,j) + (b-a). But Φ.symm(n + (b-a)) has first coordinate i+1 (established by the α function) and second coordinate j' which may differ from j.

Hmm, let me look more carefully. φ(i,j) = i*(b-a) + j*b. Then n + (b-a) = φ(i,j) + (b-a) = (i+1)*(b-a) + j*b = φ(i+1, j). So Φ.symm(n+(b-a)) = (i+1, j), meaning j' = j!

But wait, the Lean code sets j' separately and doesn't assume j' = j. Let me check... In the proof at line 1074:
```
have hχ_nba : χ (n + ↑(b - a)) = f (i + 1, j') :=
    congr_arg f (Prod.ext (by rw [hΦ_cycle, hα_ba, ← hΦ_cycle]) rfl)
```
This proves the first coordinate is i+1, but the second coordinate j' is just whatever Φ.symm gives. It does equal j in reality, but the proof doesn't need that fact because `color_covers_even` works for independent j₁, j₂.

OK so for Case 2a, j₁ and j₂ are independent in the coverage lemma, and it works because the parity-flip property holds everywhere. But for Case 2b, with independent j₁ and j₂, the coverage can fail (as shown above for e₁=3, j₁=1, j₂=0).

So for Case 2b we need to use the fact that j' = j. Let me verify this once more.

φ(i, j) = i*(b-a) + j*b (in ZMod m).
n = φ(i, j).
n + (b-a) = i*(b-a) + j*b + (b-a) = (i+1)*(b-a) + j*b = φ(i+1, j).

So Φ.symm(n + (b-a)) = (i+1, j), hence j' = j.

This means we need to prove j' = j in the Lean formalization and then use a coverage lemma with j₁ = j₂:

∀ i j k, k = f(i,j) ∨ k = f(i,j+1) ∨ k = f(i+1,j) ∨ k = f(i+1,j+1)

With j the SAME in both rows. Then the degenerate-position argument works: if even pair is {1,1} then j = e₁-2; if odd pair is {2,2} then j = 0; but j is the same, so e₁-2 = 0, contradicting e₁ ≥ 3.

This is a key difference from Case 2a! In Case 2a, the coverage lemma works for arbitrary j₁,j₂ because of the parity-flip property. In Case 2b, we need j₁ = j₂ and must prove this in the formalization.

## Revised Lemma 9: Coverage with same j

**Statement**: For any cycle index i, position j, and target color k ∈ Fin 3, assuming e₁ ≥ 3:
  k ∈ {f(i,j), f(i,j+1), f(i+1,j), f(i+1,j+1)}

**Proof**:
**k = 1**: The even-cycle row contains 1 (Lemma 3).
**k = 2**: The odd-cycle row contains 2 (Lemma 4).
**k = 0**: Suppose not. Even row has no 0 → both 1 → j.val = e₁−2 (Lemma 5). Odd row has no 0 → both 2 → j.val = 0 (Lemma 6). So e₁−2 = 0, contradicting e₁ ≥ 3 (Lemma 8). ∎

## Revised Lemma 10: Main proof

The main proof needs an additional step compared to Case 2a: proving that j' = j (i.e., Φ.symm(n + (b−a)) has the same second coordinate as Φ.symm(n)). This follows from the explicit formula for φ.

Specifically, define φ and prove:
1. φ(i, j) + (b−a) = φ(i+1, j) (not j' — same j)
2. Therefore Φ.symm(x + (b−a)) = ((Φ.symm x).1 + 1, (Φ.symm x).2)

Then the translate {n, n+b, n+(b-a), n+(2b-a)} maps to:
- f(i, j), f(i, j+1), f(i+1, j), f(i+1, j+1)

And the coverage lemma with same j applies.
