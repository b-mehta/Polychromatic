/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Berso.Main
import PolychromaticSite.Expanders

-- This gets access to most of the blog genre
open Verso Genre Blog

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Code.External

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../Lean"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Polychromatic.Main"

#doc (Page) "Polychromatic Colourings" =>

# Overview

This repository provides a formalisation in the Lean 4 theorem prover of results related to
polychromatic colourings of integers. Given a finite set {anchorTerm final}`S` of integers, a
colouring of the integers is called {anchorTerm final}`S`-polychromatic if every translate of
{anchorTerm final}`S` contains an element of each colour class. In other words, for every integer
$`n` and every colour $`c`, there exists some element $`s \in S` such that $`n + s` has colour $`c`.

Two primary targets of this repository are:
- Formalise Erdős and Lovász' solution to Strauss' conjecture on the existence of polychromatic
  colourings of sets of bounded size by any number of colours.
- Formalise the result that every set of size `4` has a polychromatic `3`-colouring, due to
  Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot, and Young.

The first of these requires results from probability theory and topology, as well as some calculus.
The second is more combinatorial, and the informal proof requires a large computer search to verify
around 4 million cases.

At the moment, we have achieved the first of these goals, and the computational part of the second
is completed, but not the non-computational aspects of the proof.

# Mathematical Background

## The Polychromatic Number

The central object of study is the *polychromatic number* $`p(S)` of a finite set $`S` of integers.
This is defined as the maximum number of colours possible in an $`S`-polychromatic colouring. Since
any $`S`-polychromatic colouring must hit every colour at every translate, the number of colours
cannot exceed $`|S|`, so $`p(S) \leq |S|`.

## Strauss' Conjecture

The *Strauss function* $`m(k)` is defined as the smallest $`m` such that every set of size at least
$`m` has a polychromatic $`k`-colouring. Equivalently, $`m(k) \leq m` if and only if every set of
size at least $`m` has $`p(S) \geq k`.

Strauss conjectured that $`m(k)` is well-defined for all $`k` -- that is, for any $`k`, there exists
some threshold $`m` beyond which all sets admit $`k`-polychromatic colourings. This was proved by
Erdős and Lovász using the Local Lemma in 1975.

## Sets of size four

A result of Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot, and Young establishes that
$`m(3) \leq 4`, meaning every set of 4 integers admits a 3-polychromatic colouring. Combined with
the fact that the set $`\{0, 1, 3\}` has polychromatic number exactly 2 (giving $`m(3) > 3`), this
shows $`m(3) = 4$. A consequence of this result is Newman's conjecture, though this consequence is
not yet formalised.

The following diagram demonstrates the dependencies of these results.

```graph
graph TD

A[Lovász local lemma]
B["$$m(k)\;$$ is well-defined (EL)"]

A --> B

B --> C["$$m(k) \leq 3k^2$$"]
C --> D["$$m(k) \leq (3+o(1))\;k\, \log\, k$$"]

B --> G["$$p(S) \geq 3\;\text{ if }\;\#S = 4\;\text{ and diam}(S) \lt 289$$"]
G --> H["$$p(S) \geq 3\;\text{ if }\;\#S = 4$$"]

classDef green  fill:#f0fdf4,stroke:#16a34a,stroke-width:1px,color:#14532d,rx:5px,ry:5px;
classDef blue   fill:#eff6ff,stroke:#2563eb,stroke-width:1px,color:#1e3a8a,rx:5px,ry:5px,stroke-dasharray: 3 3;

class A,C,D,G green;
class B green;
class H blue
```

# The Lovász Local Lemma Approach

The key tool for proving Strauss' conjecture is the *Lovász local lemma*, a powerful result in
probabilistic combinatorics. The lemma shows that if we have a collection of "bad" events, each of
which has relatively small probability and is "mostly independent" of the others, then with positive probability
*none* of the bad events occur.

## The Symmetric Local Lemma

In its most common application, the symmetric form, we have events $`A_1, \ldots, A_n` where each event:
- has probability at most $`p`, and
- is independent of all but at most $`d` other events,

then if $`e \cdot p \cdot (d + 1) \leq 1`, there exists an outcome avoiding all bad events.

## Application to Polychromatic Colourings

To prove that a set $`S` of size $`m` admits a $`k`-polychromatic colouring, we:

1. Consider a random colouring where each integer is coloured uniformly at random from $`k` colours.
2. For each translate $`n + S` and each colour $`c`, define a "bad event" as the event that no
   element of $`n + S` receives colour $`c`.
3. The probability of a bad event is $`(1 - 1/k)^m`, which is small when $`m` is large relative
   to $`k`.
4. Bad events for translates $`n + S` and $`n' + S` are independent unless the translates overlap,
   which bounds the dependency.

The Local Lemma works for finitely many translations. The Rado selection principle (a topological
compactness argument) extends this to all translations. Then straightforward analysis gives the
bound $`m(k) \leq 3k^2`, and a more careful asymptotic analysis gives $`m(k) \leq (3 + o(1)) k \log k`.
This latter bound is optimal up to constant factors (the true value is $`(1 + o(1)) k \log k`).

# The Four-Three Problem

The statement that every set of 4 integers admits a 3-polychromatic colouring is known as the
*four-three problem*. The proof combines theoretical reductions with exhaustive computational
verification.

## Theoretical Reductions

Without loss of generality, we may assume:
1. The minimum element of $`S` is 0 (by translation invariance).
2. The elements are coprime (scaling preserves the polychromatic number in torsion-free groups).
3. The elements satisfy certain ordering conditions.

These reductions allow us to focus on quadruples of the form $`\{0, a, b, c\}` with
$`0 < a < b < c`, $`a + b \leq c`, and $`\gcd(a, b, c) = 1`.

## Computational Verification

For quadruples with $`c < 289`, the proof is completed by computational verification. The approach
uses:
1. *Periodic colourings*: A colouring with period $`q$ is represented as a function
   $`\mathbb{Z} \to \text{Fin } 3$ that repeats every $`q` integers.
2. *Bit vector encoding*: Each period-$`q` colouring is encoded as three bit vectors (one per
   colour), enabling efficient verification that every translate hits all colours.
3. *Residue shortcuts*: Certain cases can be quickly discharged using simple modular arithmetic
   (e.g., if $`a \equiv 1`, $`b \equiv 2 \pmod 3`).

The C++ code in the `Generation` directory produces colouring witnesses for the vast majority of the
900,000 sets, but for the cases where a large ($`\geq 30`) period $`q` is necessary, this algorithm
is too slow. For these, we use Z3Py to find a colouring instead. These are then verified in Lean
using metaprogramming to construct proof terms.

## Current Status

The computational verification for $`c < 289` is complete in Lean. The remaining theoretical part
(combining this with the local lemma for large cases) is in progress.

# Definitions

```anchor IsPolychrom (module := Polychromatic.Colouring)
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
```

```anchor HasPolychromColouring (module := Polychromatic.Colouring)
def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ
```

Then, we define the polychromatic number of {anchorTerm final}`S` to be the maximum number of
colours possible in an {anchorTerm final}`S`-polychromatic colouring.

```
def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}
```

Strauss asked the question of if, for all `k`, there exists an upper bound `m` such that any set of
size at least `m` has a polychromatic `k`-colouring. This is answered affirmatively by the Lovász
local lemma approach described above.

# Key Formalised Results

## The Strauss Function

The Strauss function is formalised as:

```
noncomputable def straussFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}
```

Key results include:
- `straussFunction_spec`: Sets of size at least `straussFunction k` have `k`-colourings.
- `le_straussFunction_self`: $`k \leq m(k)` for all $`k`.
- `straussFunction_le_of_forall_three_mul_sq`: $`m(k) \leq 3k^2`.
- `straussFunction_isLittleO`: Asymptotically, $`m(k) \leq (3 + o(1)) k \log k`.

## The Main Theorem (Partial)

The main theorem states that every set of 4 integers has a 3-polychromatic colouring:

```anchor final (module := Polychromatic.Main)
/-- Every set `S` of 4 integers has a 3-polychromatic colouring. -/
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S := by
  sorry
```

The `sorry` indicates this proof is incomplete, but the computational part (verifying small cases)
is done.

# References

- Erdős, Paul; Lovász, László (1975). "Problems and results on 3-chromatic hypergraphs and some
  related questions". *Infinite and finite sets (Colloq., Keszthely, 1973), Vol. II*, Colloq. Math.
  Soc. János Bolyai, Vol. 10, North-Holland, pp. 609–627.
- Axenovich, Maria; Goldwasser, John; Lidický, Bernard; Martin, Ryan; Offner, David; Talbot, John;
  Young, Michael (2019). "Polychromatic colorings on the integers". *Integers* 19, A18.
- Alon, Noga; Spencer, Joel H. (2016). *The Probabilistic Method*, 4th edition. John Wiley & Sons.
- de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs and a problem in the
  theory of relations". *Indagationes Mathematicae* 13, pp. 371–373.

# Repository Structure

The repository is organised as follows:

: `Generation`

  C++ and Python code for generating explicit periodic colourings. The main output is
  `full-colors.log`, which contains around 900,000 colouring witnesses used by the Lean
  verification.

: `Lean`

  The formal Lean 4 proofs, including:
  - `Colouring.lean`: Core definitions of polychromatic colourings
  - `LocalLemma.lean`: The Lovász local lemma
  - `Existence.lean`: Existence results via probabilistic methods
  - `PolychromNumber.lean`: The polychromatic number and Strauss function
  - `FourThree/`: Computational verification for the four-three problem

: `Verso`

  Lean code for generating this documentation website using the Verso framework.

: `site`

  Jekyll website source files, completed by the Verso-generated content.
