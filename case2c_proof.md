# Case 2c: Informal Proof

## Setup

We work in the setting of Main Case 2 (Multiple Cycles) from the paper
(Grytczuk, Kiefer, et al., arXiv:1704.00042, proof of Theorem 1).

**Given:**
- Integers `0 < a < b < c` with `gcd(a,b,c) = 1` and `c >= 289`.
- `m = c - a + b`, and we work in `Z_m`.
- `S = {0, b-a, b, 2b-a}` in `Z_m`.
- `d₁ = gcd(b, m)`, `d₂ = gcd(b-a, m)`, with `gcd(d₁, d₂) = 1`.
- Both `d₁ > 1` and `d₂ > 1` (Multiple Cycles case).
- `e₁ = m / d₁`, `e₂ = m / d₂`.
- The elements of `Z_m` decompose into `d₁` cycles of length `e₁`:
  `C_i = {c_{i,j} : 0 <= j < e₁}` where `c_{i,j} = i*(b-a) + j*b (mod m)`.
- Any translate of `S` has the form `{c_{i,j}, c_{i,j+1}, c_{i+1,j}, c_{i+1,j+1}}`
  (subscripts mod `d₁` and `e₁` respectively).

**Case 2c hypotheses:**
- `d₁` and `e₁` are both **odd**.
- `e₁ <= 17`.

## Goal

Construct an `S`-polychromatic 3-coloring of `Z_m`.

## Proof Outline

The strategy is to color each cycle `C_i` with one of three "shifted 012"
patterns, and show that adjacent cycles always use different patterns,
guaranteeing that the 2x2 blocks `{c_{i,j}, c_{i,j+1}, c_{i+1,j}, c_{i+1,j+1}}`
cover all 3 colors.

---

## Lemma 1: `e₂ > e₁`, hence `d₁ > d₂`

Since `e₁ * e₂ >= e₁ * d₁ = m > c >= 289` and `e₁ <= 17`, we get
`e₂ >= 289 / 17 > 17 >= e₁`. Since `d₁ * e₁ = m = d₂ * e₂` and `e₂ > e₁`,
we conclude `d₁ > d₂`.

**Purpose:** Establishes that `d₁` is the larger of the two GCD values (not
a multiple of 3), while `d₂` is the smaller one.

## Lemma 2: `d₂` is a multiple of 3, hence `e₁` is a multiple of 3

By the problem setup, `d₁` is chosen as the smallest of `{d₁, d₂}` that is
not a multiple of 3. Since `d₁ > d₂` (Lemma 1), `d₁` is NOT the smallest.
The WLOG assumption says we pick the smallest that's not a multiple of 3 to
be `d₁`. So for `d₁ > d₂` to hold while `d₁` is chosen, `d₂` must be a
multiple of 3.

Since `gcd(d₁, d₂) = 1` and `3 | d₂`, we have `3 ∤ d₁`. Since `d₁` and `e₁`
are both odd and `m = d₁ * e₁`, and `m = d₂ * e₂`, with `3 | d₂` and
`gcd(d₁, d₂) = 1`, the factor of 3 in `m` must come from `e₁` (since `3 ∤ d₁`).
Therefore `3 | e₁`.

**Purpose:** Shows that each cycle length `e₁` is divisible by 3, which is
crucial for the three-phase coloring pattern.

## Lemma 3: `e₁ ∈ {3, 9, 15}` (the possible odd values ≤ 17 divisible by 3)

Since `e₁` is odd, `e₁ <= 17`, and `3 | e₁`, the possible values are
`e₁ ∈ {3, 9, 15}`.

**Purpose:** Constrains `e₁` to exactly three cases.

## Lemma 4: `d₁ >= 3`

Since `d₁ > 1` and `d₁` is odd, we have `d₁ >= 3`.

**Purpose:** Needed for the coloring pattern — we need at least 3 cycles
for the alternating pattern to work, and d₁ is odd so d₁ >= 3 suffices.

## Lemma 5: Definition of the three coloring patterns

Define three patterns on a cycle of length `e₁` (where `3 | e₁`):
- **Pattern 0:** `012012...012` (repeating `012` exactly `e₁/3` times)
- **Pattern 1:** `120120...120` (repeating `120` exactly `e₁/3` times)
- **Pattern 2:** `201201...201` (repeating `201` exactly `e₁/3` times)

Formally, Pattern `p` assigns color `(j + p) mod 3` to position `j` in the
cycle. Since `3 | e₁`, the pattern is well-defined on `Z_{e₁}`: position
`j` gets color `(j + p) mod 3`, and since `e₁ ≡ 0 (mod 3)`, this wraps
correctly.

**Purpose:** Defines the building blocks for the coloring.

## Lemma 6: Two consecutive positions in the same pattern get different colors

For any pattern `p` and position `j`:
`(j + p) mod 3 ≠ (j + 1 + p) mod 3`.

This is immediate since consecutive integers have different residues mod 3.

**Purpose:** Shows that within a single cycle, consecutive elements get
different colors (so the pair `{c_{i,j}, c_{i,j+1}}` uses 2 distinct colors).

## Lemma 7: Different patterns on the same position yield different colors

If `p₁ ≠ p₂` (as elements of `{0, 1, 2}`), then for any position `j`:
`(j + p₁) mod 3 ≠ (j + p₂) mod 3`.

**Purpose:** Shows that if two adjacent cycles use different patterns, then
at any fixed position `j`, the colors from the two cycles are different.

## Lemma 8: Adjacent cycles with different patterns produce all 3 colors

Given cycles `C_i` and `C_{i+1}` colored with patterns `p_i ≠ p_{i+1}`,
for any `j₁, j₂`, the four-element set
`{color(i, j₁), color(i, j₁+1), color(i+1, j₂), color(i+1, j₂+1)}`
contains all 3 colors.

**Proof:** By Lemma 6, `{color(i, j₁), color(i, j₁+1)}` contains 2 distinct
colors. These 2 colors include at most 2 of the 3 colors, so the missing
color `c` satisfies `c ≠ color(i, j₁)` and `c ≠ color(i, j₁+1)`.
By Lemma 7 (applied with the two patterns), the colors from cycle `i+1` are
different from those of cycle `i` at corresponding positions. In fact, since
there are only 3 colors and the pair from `C_i` misses exactly one, and each
color from `C_{i+1}` at position `j₂` or `j₂+1` differs from the
corresponding `C_i` values, at least one of `color(i+1, j₂)` or
`color(i+1, j₂+1)` must be the missing color.

More precisely: the pair `{color(i+1, j₂), color(i+1, j₂+1)}` also consists
of 2 distinct colors (Lemma 6). The pattern `p_{i+1} ≠ p_i`, so
`color(i+1, j₂) = (j₂ + p_{i+1}) mod 3`. The three colors from patterns
`p_i` and `p_{i+1}` at positions `j₁, j₁+1, j₂, j₂+1` span `{0,1,2}`
because `p_i ≠ p_{i+1}` implies the two 2-element color sets from the two
cycles together cover all 3 values.

**Purpose:** This is the core polychromaticity argument.

## Lemma 9: The pattern assignment makes adjacent cycles use different patterns

Assign patterns to cycles as follows:
- For `i = 0, 2, 4, ..., d₁-3` (even indices up to `d₁-3`): use Pattern 0.
- For `i = 1, 3, 5, ..., d₁-2` (odd indices up to `d₁-2`): use Pattern 1.
- For `i = d₁-1` (the last cycle): use Pattern 2.

Then for every `i ∈ {0, ..., d₁-1}`, cycle `i` and cycle `(i+1) mod d₁`
use different patterns:
- `i` even, `i < d₁-1`: pattern 0 vs pattern 1. ✓
- `i` odd, `i < d₁-2`: pattern 1 vs pattern 0. ✓
- `i = d₁-2` (even since `d₁` is odd): pattern 0 vs pattern 2. ✓
- `i = d₁-1`: pattern 2 vs pattern 0 (cycle 0). ✓

**Purpose:** Verifies the key condition for Lemma 8 to apply.

## Lemma 10: Assembly — the coloring is S-polychromatic

Combine everything:
1. The orbit map `φ : Z_{d₁} × Z_{e₁} → Z_m` defined by
   `φ(i,j) = i*(b-a) + j*b` is a bijection (reuse from Case 2a/2d infrastructure).
2. Define the coloring `χ : Z_m → Fin 3` by
   `χ(φ(i,j)) = (j + pattern(i)) mod 3`
   where `pattern(i)` is defined in Lemma 9.
3. Any translate of `S` meeting cycles `i` and `i+1` has the form
   `{c_{i,j}, c_{i,j+1}, c_{i+1,j'}, c_{i+1,j'+1}}`.
4. By Lemma 9, `pattern(i) ≠ pattern(i+1 mod d₁)`.
5. By Lemma 8, the four colors cover all of `{0, 1, 2}`.

Therefore `χ` is an `S`-polychromatic 3-coloring.

**Purpose:** Wraps up the proof of Case 2c.
