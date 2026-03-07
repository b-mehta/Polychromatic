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
polychromatic colourings of integers. Given a finite set $`S` of integers, a
colouring of the integers is called $`S`-polychromatic if every translate of
$`S` contains an element of each colour class. In other words, for every integer
$`n` and every colour $`c`, there exists some element $`s \in S` such that $`n + s` has colour $`c`.

For example, consider the set $`S = \{0, 1\}`. A 2-colouring of the integers is $`S`-polychromatic
if every pair of consecutive integers $`\{n, n+1\}` contains both colours. The standard alternating
colouring (even numbers red, odd numbers blue) achieves this, so $`S` admits a 2-polychromatic
colouring. In fact, this is optimal: no 3-colouring can be $`S`-polychromatic since each pair would
need to contain all three colours but only has two elements.

Using fewer colours makes it *easier* to be polychromatic: if every translate of $`S` hits
all $`k` colours, it certainly hits any subset of them. Similarly, larger sets are easier to colour
polychromatically, since there are more elements available in each translate to cover the required
colours. So a natural question is: how large must $`S` be to guarantee a $`k`-polychromatic
colouring exists?

Two primary targets of this repository are:
- Formalise Erdős and Lovász' solution to Strauss' conjecture on the existence of polychromatic
  colourings of sets of bounded size by any number of colours.
- Formalise the result that every set of size $`4` has a polychromatic $`3`-colouring, due to
  Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot, and Young.

The first of these requires results from probability theory and topology, as well as some calculus.
The second is more combinatorial, and the informal proof requires a large computer search to verify
around 4 million cases.

At the moment, we have achieved the first of these goals, and the computational part of the second
is completed, but not the non-computational aspects of the proof.

# Repository Structure

The repository is organised as follows:

: `Generation`

  C++ and Python code using Z3 for generating explicit periodic colourings. The main output is
  `full-colors.log`, which contains colouring witnesses used by the Lean verification.

: `Lean`

  The formal Lean 4 proofs, including:
  - `Colouring.lean`: Core definitions of polychromatic colourings
  - `LocalLemma.lean`: The Lovász local lemma
  - `Existence.lean`: Existence results via probabilistic and topological methods
  - `FourThree/`: Computational verification for the four-three problem

: `Verso`

  Lean code for generating this documentation website using the Verso framework.

: `site`

  Jekyll website source files, completed by the Verso-generated content.

# Mathematical Background

## Definitions

We first define the predicate for a colouring to be polychromatic for a set.

```anchor IsPolychrom (module := Polychromatic.Colouring)
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
```

This says that a colouring $`\chi` is $`S`-polychromatic if for every translation $`n` and every
colour $`k`, there exists an element $`a \in S` such that $`n + a` has colour $`k`. In other words,
every translate $`n + S` contains all colours.

We can then say a set $`S` admits a $`K`-coloured polychromatic colouring if there exists some
colouring $`\chi : G \to K` that is $`S`-polychromatic.

```anchor HasPolychromColouring (module := Polychromatic.Colouring)
def HasPolychromColouring (K : Type*) (S : Finset G) : Prop :=
  ∃ χ : G → K, IsPolychrom S χ
```

## The Polychromatic Number

The central object of study is the *polychromatic number* $`p(S)` of a finite set $`S` of integers.
This is defined as the maximum number of colours possible in an $`S`-polychromatic colouring.

Why does this maximum exist?
Any $`S`-polychromatic colouring must hit every colour at every translate of $`S`.
Consider any translate $`n + S` — it has exactly $`|S|` elements, and each colour must appear among
them.
Therefore the number of colours cannot exceed $`|S|`, so $`p(S) \leq |S|`.

In Lean, we formalise the polychromatic number directly.

```anchor polychromNumber (module := Polychromatic.PolychromNumber)
def polychromNumber (S : Finset G) : ℕ :=
  sSup {n | HasPolychromColouring (Fin n) S}
```

We also establish the upper bound $`p(S) \leq |S|`.

```anchor polychromNumber_le_card (module := Polychromatic.PolychromNumber)
lemma polychromNumber_le_card : polychromNumber S ≤ #S := by
```

As noted above, every pair of distinct integers has polychromatic number exactly 2.

```anchor polychromNumber_pair (module := Polychromatic.PolychromNumber)
@[simp] lemma polychromNumber_pair [DecidableEq G] [IsAddTorsionFree G] {x y : G} (hxy : x ≠ y) :
    polychromNumber {x, y} = 2 := by
```

Can we do better with three elements? Consider the set $`\{0, 1, 3\}` and try to 3-colour the
integers polychromatically. Since $`\{0, 1, 3\}` has three elements, each translate must contain all
three colours, meaning the colouring restricted to each translate is a bijection onto the three
colours. In particular, the elements $`0`, $`1`, $`3` must receive three distinct colours. Now
consider the element $`2`: it must receive one of the three colours. Each choice leads to a
contradiction:
- If $`2` gets the same colour as $`1`, the translate $`\{1, 2, 4\}` has at most two distinct
  colours among its three elements — but all three are needed.
- If $`2` gets the same colour as $`0`, the translate $`\{-1, 0, 2\}` gives the same contradiction.
- If $`2` gets the same colour as $`3`, the translate $`\{2, 3, 5\}` gives the same contradiction.

So no 3-colouring of $`\{0, 1, 3\}` is polychromatic. Since $`\{0, 1, 3\}` contains a pair, it
has polychromatic number at least 2, giving $`p(\{0, 1, 3\}) = 2`. This is formalised as:

```anchor polychromNumber_three_eq_two (module := Polychromatic.PolychromNumber)
lemma polychromNumber_three_eq_two : polychromNumber (G := ℤ) {0, 1, 3} = 2 := by
```

## Strauss' Conjecture

If we fix a set $`S`, there is always some number of colours that works — at most $`|S|`. But what
if we turn the question around and fix the number of colours? Is there a set size large enough that
*every* set of that size is guaranteed to have a polychromatic $`k`-colouring?

The *Strauss function* $`m(k)` is defined as the smallest $`m` such that every set of size at least
$`m` has a polychromatic $`k`-colouring. Equivalently, $`m(k) \leq m` if and only if every set of
size at least $`m` has $`p(S) \geq k`.

Strauss conjectured that $`m(k)` is *finite* for all $`k`.
This is not obvious: while $`p(S) \leq |S|` tells us that small sets cannot have many colours,
it does not immediately imply that large sets must have many colours.
Strauss' conjecture asserts that size alone guarantees a minimum polychromatic number.

This was proved by Erdős and Lovász using the Local Lemma in 1975.

```anchor straussFunction (module := Polychromatic.LovaszFunction)
noncomputable def straussFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ S : Finset ℤ, m ≤ #S → HasPolychromColouring (Fin k) S}
```

The key property of the Strauss function is that sets of sufficient size have polychromatic colourings.

```anchor straussFunction_spec (module := Polychromatic.LovaszFunction)
lemma straussFunction_spec {k : ℕ} (hk : k ≠ 0) (S : Finset ℤ)
    (hkS : straussFunction k ≤ #S) :
    HasPolychromColouring (Fin k) S :=
  Nat.sInf_mem (straussFunction_nonempty hk) S hkS
```

The first few values of the Strauss function are easy to compute: $`m(1) = 1` (every nonempty set
can be 1-coloured polychromatically) and $`m(2) = 2` (every pair has polychromatic number 2). The
main theorem of this project establishes $`m(3) = 4`: the set $`\{0, 1, 3\}` shows
$`m(3) > 3`, and the result of Axenovich et al. shows $`m(3) \leq 4`.

## Sets of size four

The following diagram shows the dependencies between the main results.

```graph
graph TD

A[Lovász local lemma]
B["$$m(k)\;$$ is well-defined (EL)"]

A --> B

B --> C["$$m(k) \leq 3k^2$$"]
C --> D["$$m(k) \leq (3+o(1))\;k\, \log\, k$$"]

B --> E["$$m(3) = 4$$"]

G["$$p(S) \geq 3\;\text{ if }\;\#S = 4\;\text{ and diam}(S) \lt 289$$"]
G --> H["$$p(S) \geq 3\;\text{ if }\;\#S = 4$$"]
H --> E

classDef green  fill:#f0fdf4,stroke:#16a34a,stroke-width:1px,color:#14532d,rx:5px,ry:5px;
classDef blue   fill:#eff6ff,stroke:#2563eb,stroke-width:1px,color:#1e3a8a,rx:5px,ry:5px,stroke-dasharray: 3 3;

class A,C,D,G green;
class B green;
class E,H blue
```

# Proving Strauss' conjecture

The key tool for proving Strauss' conjecture is the *Lovász local lemma*, a classical result in
probabilistic combinatorics. The idea is to colour randomly: if the "bad" events (a translate
missing some colour) each have small probability and are mostly independent of each other, the
Local Lemma guarantees that with positive probability *none* of the bad events occur.

## The Symmetric Local Lemma

The most commonly used form is the symmetric version. If we have events $`A_1, \ldots, A_n` where each event:
- has probability at most $`p`, and
- is independent of all but at most $`d` other events,

then if $`e p (d + 1) \leq 1`, there exists an outcome avoiding all bad events.

## Application to Polychromatic Colourings

To prove that a set $`S` of size $`m` admits a $`k`-polychromatic colouring, we fix a finite set
$`X` of integers from which we will choose translations, then:

1. Consider a random colouring where each element of $`X + S` is coloured uniformly at random from
   $`k` colours.
2. For each translate $`n + S` with $`n \in X` and each colour $`c`, define a "bad event" as the
   event that no element of $`n + S` receives colour $`c`.
3. The probability of a bad event is $`(1 - 1/k)^m`, which is small when $`m` is large relative
   to $`k`.
4. Bad events for translates $`n + S` and $`n' + S` are independent unless the translates overlap,
   which bounds the dependency.

The Local Lemma then guarantees that with positive probability, none of the bad events occur for
any $`n \in X`. This gives a polychromatic colouring on the finite set $`X`.

However, the Local Lemma only applies to *finitely many* events. This is the key limitation: we get
colourings on arbitrarily large finite subsets of $`\mathbb{Z}`, but not yet a single global
colouring.

## The Rado Selection Principle

To extend from finite to infinite, we use the *Rado selection principle*, a compactness argument
based on Tychonoff's theorem (specifically, the finite intersection property for compact spaces).

The Rado selection principle states that if we have a family of functions $`g_F : F \to K` indexed
by finite sets $`F`, where $`K` is finite, then there exists a global function $`\chi : \mathbb{Z} \to K`
such that for every finite set $`F`, there is a larger finite set $`F' \supseteq F` where $`\chi`
and $`g_{F'}` agree on $`F`.

Here is the key idea: suppose that for every finite set $`X \subseteq \mathbb{Z}`, we can find an
$`S`-polychromatic colouring $`g_X` of $`X`. We want to "glue" these together into a single global
colouring $`\chi : \mathbb{Z} \to K`. The difficulty is that $`g_X` and $`g_Y` might disagree on
their common domain $`X \cap Y`.

The Rado selection principle resolves this: it guarantees there exists a global colouring $`\chi`
such that for every finite set $`F`, there is some larger finite set $`F' \supseteq F` where $`\chi`
agrees with $`g_{F'}` on $`F`. Since $`g_{F'}` is $`S`-polychromatic on $`F'`, any translate
$`n + S \subseteq F` hits all colours under $`g_{F'}`, and hence under $`\chi`. Since this holds
for all finite $`F` containing any given translate, $`\chi` is $`S`-polychromatic globally.

This kind of compactness argument appears throughout combinatorics (e.g. the de Bruijn–Erdős
theorem on graph colouring), so isolating it as a standalone lemma is useful.

In Lean, the Rado selection principle is formalised as follows.

```anchor rado (module := Polychromatic.Compactness)
theorem Finset.rado_selection {α : Type*} {β : α → Type*}
    [∀ a, Finite (β a)]
    (g : (s : Finset α) → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α,
      ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by
```

By applying the Local Lemma to each finite set $`X` to get colourings $`g_X`, and then using Rado
selection, we obtain a global colouring $`\chi` that is $`S`-polychromatic. In Lean, the
combination is `exists_of_le`:

```anchor exists_of_le (module := Polychromatic.Existence)
lemma exists_of_le {k m : ℕ} {S : Finset G} (hm : #S = m) (hm₂ : 2 ≤ m) (hk : k ≠ 0)
    (hkm : polychromColouringBound k m) :
    HasPolychromColouring (Fin k) S := by
```

In fact, this result holds for any abelian group $`G`, not just $`\mathbb{Z}` — neither the Local
Lemma nor the Rado selection principle use any specific properties of the integers, so the bound
depends only on $`k` and $`|S|`.

## Bounds on the Strauss Function

Straightforward analysis of the probability bounds gives the quadratic upper bound:

```anchor straussFunction_le_of_forall_three_mul_sq (module := Polychromatic.LovaszFunction)
lemma straussFunction_le_of_forall_three_mul_sq {k : ℕ} :
    straussFunction k ≤ 3 * k ^ 2 := by
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

# Sets of Size Four

The proof that $`m(3) = 4` combines theoretical reductions with exhaustive computational
verification. The original paper by Axenovich et al. noted: "It is possible, though tedious, to prove the entire
theorem by hand. Thus in the interest of simplifying the exposition, we verified using a computer
search..." — a pragmatic choice that becomes especially relevant for formalisation.

## Theoretical Reductions

The proof proceeds by a chain of without-loss-of-generality reductions that narrow the set of
cases we need to check.

1. *Translation invariance* (`suffices_minimal`): We may assume the minimum element of $`S` is 0,
   since the polychromatic number is invariant under translation.
2. *Ordered triples* (`suffices_triple`): We may write $`S = \{0, a, b, c\}` with
   $`0 < a < b < c`.
3. *The flip* (`suffices_flip`): If $`a + b > c`, we can replace $`S` with
   $`\{0, c-b, c-a, c\}`, which satisfies $`(c-b) + (c-a) \leq c`. This uses the fact that the
   polychromatic number is invariant under negation.
4. *Coprimality* (`suffices_gcd`): We may assume $`\gcd(a, b, c) = 1`, since scaling preserves
   the polychromatic number in torsion-free groups.
5. *Case split* (`suffices_cases`): The remaining cases split into $`c < 289` (handled
   computationally) and $`c \geq 289` (handled by the existence bound from Strauss' conjecture).

After these reductions, we are left with quadruples $`\{0, a, b, c\}` where
$`0 < a < b < c < 289`, $`a + b \leq c`, and $`\gcd(a, b, c) = 1`. There are approximately
$`\binom{288}{3} \approx 4` million total triples, reduced to around 900,000 after applying
coprimality and the flip reduction.

## Computational Verification

The original paper included a C++ program for verifying the small cases, and a manual proof was
written in John Goldwasser's notes but was never published.

For the formalisation, we took a certificate-based verification approach. We do not need to trust
any search code — we only need to verify that its output (explicit colourings) actually works.

For quadruples with $`c < 289`, we first search for explicit periodic colourings using C++. This
algorithm searches for colourings with period $`q` up to 30. For the vast majority of the 900,000
sets, this succeeds. For the few hundred stubborn cases where a period greater than 30 is necessary,
we use Z3Py (a Python interface to the Z3 SMT solver) to find colourings instead.

Once witnesses are found, Lean verifies them all using three key steps:
1. *Periodic colourings*: A colouring with period $`q` is represented as a function
   $`\mathbb{Z}/q\mathbb{Z} \to \text{Fin } 3` that repeats.
2. *Bit vector encoding*: Each period-$`q` colouring is encoded as three bit vectors (one per
   colour), enabling efficient verification that every translate hits all colours.
3. *Residue shortcuts*: Certain cases can be quickly discharged using simple modular arithmetic
   (e.g., if $`a \equiv 1`, $`b \equiv 2 \pmod 3`).

The crucial point is that Lean does not trust the C++ or Z3 code at all. The external solvers
produce candidate colourings, and Lean independently checks each one. This is the certificate-based
approach: separate search from verification.

## Current Status

The computational verification for $`c < 289` is complete in Lean. The remaining theoretical part
is in progress.

## The Main Theorem (Partial)

The main theorem states that every set of 4 integers has a 3-polychromatic colouring:

```anchor final (module := Polychromatic.Main)
/-- Every set `S` of 4 integers has a 3-polychromatic colouring. -/
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S :=
```

# Formalization Reflections

The proof draws on probability, topology, and calculus — all formalized using
[mathlib](https://github.com/leanprover-community/mathlib4), Lean's mathematical library.
Probability theory, measure theory, and combinatorics all live in the same system and can be
composed directly: we apply the Local Lemma to a uniform probability measure, use topological
compactness via Rado selection, and perform real analysis for the asymptotic bound, all within
one proof.

The search for general results also led to new formalisations. The Rado selection lemma, for
instance, was not previously in mathlib, and its proof via Tychonoff's theorem provides a reusable
tool for other compactness arguments in combinatorics.

For the four-three problem, the certificate-based approach separates the *search* (C++, Z3 — any
heuristic or solver) from the *verification* (Lean's trusted kernel). The search code can be
arbitrarily complex or heuristic; only the output needs to be correct, and Lean checks that.

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
