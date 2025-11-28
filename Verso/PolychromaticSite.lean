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

For example, consider the set $`S = \{0, 1\}$. A 2-colouring of the integers is $`S`-polychromatic
if every pair of consecutive integers $`\{n, n+1\}$ contains both colours. The standard alternating
colouring (even numbers red, odd numbers blue) achieves this, so $`S` admits a 2-polychromatic
colouring. In fact, this is optimal: no 3-colouring can be $`S`-polychromatic since each pair would
need to contain all three colours but only has two elements.

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

# Repository Structure

The repository is organised as follows:

: `Generation`

  C++ and Python code for generating explicit periodic colourings. The main output is
  `full-colors.log`, which contains colouring witnesses used by the Lean verification.

: `Lean`

  The formal Lean 4 proofs, including:
  - `Colouring.lean`: Core definitions of polychromatic colourings
  - `LocalLemma.lean`: The Lovász local lemma
  - `Existence.lean`: Existence results via probabilistic methods
  - `PolychromNumber.lean`: The polychromatic number
  - `LovaszFunction.lean`: The Strauss function and its bounds
  - `FourThree/`: Computational verification for the four-three problem

: `Verso`

  Lean code for generating this documentation website using the Verso framework.

: `site`

  Jekyll website source files, completed by the Verso-generated content.

# Mathematical Background

## The Polychromatic Number

The central object of study is the *polychromatic number* $`p(S)` of a finite set $`S` of integers.
This is defined as the maximum number of colours possible in an $`S`-polychromatic colouring.

Why is there a maximum? Because any $`S`-polychromatic colouring must hit every colour at every
translate of $`S`. Consider any translate $`n + S` — it has exactly $`|S|` elements, and each colour
must appear among them. Therefore the number of colours cannot exceed $`|S|`, so $`p(S) \leq |S|`.

In Lean, we formalise the polychromatic number as:

```anchor polychromNumber (module := Polychromatic.PolychromNumber)
def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}
```

The upper bound $`p(S) \leq |S|` is established by:

```anchor polychromNumber_le_card (module := Polychromatic.PolychromNumber)
lemma polychromNumber_le_card : polychromNumber S ≤ #S := by
```

## Strauss' Conjecture

The *Strauss function* $`m(k)` is defined as the smallest $`m` such that every set of size at least
$`m` has a polychromatic $`k`-colouring. Equivalently, $`m(k) \leq m` if and only if every set of
size at least $`m` has $`p(S) \geq k`.

In Lean, this is defined as:

```anchor straussFunction (module := Polychromatic.LovaszFunction)
noncomputable def straussFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}
```

The key property of the Strauss function is that sets of sufficient size have polychromatic colourings:

```anchor straussFunction_spec (module := Polychromatic.LovaszFunction)
lemma straussFunction_spec {k : ℕ} (hk : k ≠ 0) (S : Finset ℤ) (hkS : straussFunction k ≤ #S) :
    HasPolychromColouring (Fin k) S :=
  Nat.sInf_mem (straussFunction_nonempty hk) S hkS
```

Strauss conjectured that $`m(k)` is *finite* for all $`k$. This is not obvious: while $`p(S) \leq |S|`
tells us that small sets cannot have many colours, it does not immediately imply that large sets
must have many colours. Strauss' conjecture asserts that size alone guarantees a minimum polychromatic
number. This was proved by Erdős and Lovász using the Local Lemma in 1975.

## Sets of size four

A result of Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot, and Young establishes that
$`m(3) \leq 4`, meaning every set of 4 integers admits a 3-polychromatic colouring. Combined with
the fact that the set $`\{0, 1, 3\}` has polychromatic number exactly 2 (giving $`m(3) > 3`), this
shows $`m(3) = 4$. A consequence of this result is Newman's conjecture, though this consequence is
not yet formalised.

In Lean, we prove that the set $`\{0, 1, 3\}` has polychromatic number 2:

```anchor polychromNumber_three_eq_two (module := Polychromatic.PolychromNumber)
lemma polychromNumber_three_eq_two : polychromNumber (G := ℤ) {0, 1, 3} = 2 := by
```

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

To prove that a set $`S` of size $`m` admits a $`k`-polychromatic colouring, we fix a finite set
$`X` of integers from which we will choose translations, then:

1. Consider a random colouring where each element of $`X + S$ is coloured uniformly at random from
   $`k` colours.
2. For each translate $`n + S` with $`n \in X` and each colour $`c`, define a "bad event" as the
   event that no element of $`n + S` receives colour $`c`.
3. The probability of a bad event is $`(1 - 1/k)^m`, which is small when $`m` is large relative
   to $`k`.
4. Bad events for translates $`n + S` and $`n' + S` are independent unless the translates overlap,
   which bounds the dependency.

The Local Lemma then guarantees that with positive probability, none of the bad events occur for
any $`n \in X`. This gives a polychromatic colouring on the finite set $`X`.

## The Rado Selection Principle

The Local Lemma only applies to finitely many translations. To extend this to *all* of $`\mathbb{Z}`,
we use the *Rado selection principle*, a compactness argument based on Tychonoff's theorem.

The Rado selection principle states that if we have a family of functions $`g_F : F \to K$ indexed
by finite sets $`F$, where $`K$ is finite, then there exists a global function $`\chi : \mathbb{Z} \to K`
such that for every finite set $`F`, there is a larger finite set $`F' \supseteq F` where $`\chi`
and $`g_{F'}` agree on $`F$.

Here is the key idea: suppose that for every finite set $`X \subseteq \mathbb{Z}$, we can find an
$`S`-polychromatic colouring $`g_X$ of $`X`. We want to "glue" these together into a single global
colouring $`\chi : \mathbb{Z} \to K`. The difficulty is that $`g_X$ and $`g_Y$ might disagree on
their common domain $`X \cap Y$.

The Rado selection principle resolves this: it guarantees there exists a global colouring $`\chi`
such that for every finite set $`F$, there is some larger finite set $`F' \supseteq F$ where $`\chi`
agrees with $`g_{F'}` on $`F`. Since $`g_{F'}` is $`S`-polychromatic on $`F'$, any translate
$`n + S \subseteq F$ hits all colours under $`g_{F'}$, and hence under $`\chi$. Since this holds
for all finite $`F` containing any given translate, $`\chi` is $`S`-polychromatic globally.

In Lean, this is formalised as:

```
theorem Finset.rado_selection {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x
```

By applying the Local Lemma to each finite set $`X` to get colourings $`g_X`, and then using Rado
selection, we obtain a global colouring $`\chi$ that is $`S`-polychromatic.

## Bounds on the Strauss Function

Straightforward analysis of the probability bounds gives the quadratic upper bound:

```anchor straussFunction_le_of_forall_three_mul_sq (module := Polychromatic.LovaszFunction)
lemma straussFunction_le_of_forall_three_mul_sq {k : ℕ} : straussFunction k ≤ 3 * k ^ 2 := by
```

A more careful asymptotic analysis gives $`m(k) \leq (3 + o(1)) k \log k`:

```anchor straussFunction_isLittleO (module := Polychromatic.LovaszFunction)
lemma straussFunction_isLittleO :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 4,
      straussFunction k ≤ (3 + f k) * k * Real.log k := by
```

This latter bound is optimal up to constant factors (the true value is $`(1 + o(1)) k \log k`).

We also prove the easy lower bound $`k \leq m(k)`:

```anchor le_straussFunction_self (module := Polychromatic.LovaszFunction)
lemma le_straussFunction_self {k : ℕ} :
    k ≤ straussFunction k := by
```

# The Four-Three Problem

The four-three problem asks whether every set of 4 integers admits a 3-polychromatic colouring.
The proof combines theoretical reductions with exhaustive computational verification.

## Theoretical Reductions

Without loss of generality, we may assume:
1. The minimum element of $`S` is 0 (by translation invariance).
2. The elements are coprime (scaling preserves the polychromatic number in torsion-free groups).

These reductions allow us to focus on quadruples of the form $`\{0, a, b, c\}` with
$`0 < a < b < c`, $`a + b \leq c`, and $`\gcd(a, b, c) = 1`.

## Computational Verification

For quadruples with $`c < 289`, we first search for explicit periodic colourings using C++. This
algorithm searches for colourings with period $`q` up to 30. For the vast majority of the 900,000
sets, this succeeds. For the cases where a period greater than 30 is necessary, the C++ search is
too slow, so we use Z3Py (a Python interface to the Z3 SMT solver) to find colourings instead.

Why $`c < 289`? The bound 289 comes from applying the Local Lemma: when $`c \geq 289` (and hence
$`|S| = 4`), the set is large enough in "diameter" that the Local Lemma directly guarantees a
3-polychromatic colouring exists. So we only need computational verification for smaller sets.

Once witnesses are found, Lean verifies them all using three key steps:
1. *Periodic colourings*: A colouring with period $`q$ is represented as a function
   $`\mathbb{Z}/q\mathbb{Z} \to \text{Fin } 3$ that repeats.
2. *Bit vector encoding*: Each period-$`q` colouring is encoded as three bit vectors (one per
   colour), enabling efficient verification that every translate hits all colours.
3. *Residue shortcuts*: Certain cases can be quickly discharged using simple modular arithmetic
   (e.g., if $`a \equiv 1`, $`b \equiv 2 \pmod 3`).

## Current Status

The computational verification for $`c < 289` is complete in Lean. The remaining theoretical part
(combining this with the local lemma for large cases) is in progress.

# Definitions

The core definitions in Lean are:

```anchor IsPolychrom (module := Polychromatic.Colouring)
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
```

This says: a colouring $`\chi` is $`S`-polychromatic if for every translation $`n$ and every
colour $`k$, there exists an element $`a \in S$ such that $`n + a$ has colour $`k$. In other words,
every translate $`n + S$ contains all colours.

```anchor HasPolychromColouring (module := Polychromatic.Colouring)
def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ
```

This says: a set $`S$ admits a $`K`-coloured polychromatic colouring if there exists some colouring
$`\chi : G \to K$ that is $`S`-polychromatic.

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
- Rado, R. (1949). "Axiomatic treatment of rank in infinite sets". *Journal of the London
  Mathematical Society* 24, pp. 249–255.
