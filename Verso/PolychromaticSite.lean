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

This repository aims to formalise results related to polychromatic colourings of integers. Given a
finite set {anchorTerm final}`S` of integers, a colouring of the integers is called
{anchorTerm final}`S`-polychromatic if every
translate of {anchorTerm final}`S` contains an element of each colour class.

Two primary targets of this repository are:
- Formalise Erdős and Lovász' solution to Strauss' conjecture on the existence of polychromatic
  colourings of sets of bounded size by any number of colours.
- Formalise the result that every set of size `4` has a polychromatic `3`-colouring, due to
  Axenovich, Goldwasser, Lidický, Martin, Offner, Talbot, and Young; and thus formally resolve a
  conjecture of Newman.

The first of these requires results from probability theory and topology, as well as some calculus.
The second is more combinatorial, and the informal proof requires a large computer search to verify
around 4 million cases.

At the moment, we have achieved the first of these goals, and the computational part of the second
is completed, but not the non-computational aspects of the proof.

The following diagram demonstrates the dependencies of these results.
We define $`p(S)` to be the largest number of colours possible for an $`S`-polychromatic colouring,
and $`m(k)` to be the smallest $`m` such that every set of size at least $`m` has a polychromatic
$`k`-colouring. In this language, $`m(k) \leq m` if and only if every set of size at least $`m` has
$p(S) \geq k$.
Note that any $`S`-polychromatic colouring must use at least $`\#S` colours, so $`p(S) \leq \#S`,
and in particular is defined.
However it is not as immediate that $`m(k)` is well-defined: Strauss' conjecture says it is.

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

# Definitions

We formalise the notion of a polychromatic colouring in Lean. The key definition states that a
colouring `χ : G → K` is `S`-polychromatic if every translate of `S` contains an element of each
colour class. Equivalently, for every starting point `n` and every colour `k`, there exists some
element `a ∈ S` such that `χ(n + a) = k`.

```anchor IsPolychrom (module := Polychromatic.Colouring)
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
```

We then define a predicate stating that a set `S` admits a `K`-valued polychromatic colouring:

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

A fundamental observation is that the number of colours in any `S`-polychromatic colouring cannot
exceed `|S|`. This is because each translate `n + S` must contain elements of every colour, but
`n + S` has only `|S|` elements.

We also define the Strauss function $`m(k)`, which is the smallest `m` such that every set of size
at least `m` admits a polychromatic `k`-colouring. This function captures exactly how large a set
needs to be to guarantee a given number of colours.

# Strauss' Conjecture

Strauss asked the question of if, for all `k`, there exists an upper bound `m` such that any set of
size at least `m` has a polychromatic `k`-colouring. In other words: is $`m(k)` well-defined for all
`k`?

This conjecture was resolved positively by Erdős and Lovász in 1975 using the Lovász Local Lemma, a
powerful tool from probabilistic combinatorics.

# The Lovász Local Lemma

The Lovász Local Lemma is one of the main mathematical tools used in this formalisation. It provides
conditions under which a random object avoids all "bad" events simultaneously.

The symmetric version states: if we have events $`A_1, \ldots, A_n` where each event has probability
at most `p` and each event is independent of all but at most `d` other events, then if
$`e \cdot p \cdot (d + 1) \le 1`, there exists an outcome avoiding all bad events.

We formalise both the symmetric local lemma and a more general version with individual bounds. The
proof proceeds by induction on subsets, following the standard probabilistic argument.

Using the local lemma, we prove that $`m(k) \le 3k^2` for all `k`, and with more careful analysis,
we achieve the asymptotically optimal bound $`m(k) \le (3 + o(1)) k \log k`.

# The Four-Three Problem

A specific instance of the polychromatic colouring problem asks: does every set of 4 integers admit
a 3-polychromatic colouring? This was conjectured by Newman and resolved by Axenovich et al.

The approach combines two techniques:

1. **Lovász Local Lemma bound**: For sets with large diameter (specifically, diameter ≥ 289), the
   local lemma provides a probabilistic proof of existence.

2. **Computational verification**: For sets with small diameter (< 289), we verify the existence of
   3-colourings by direct computation.

The computational approach involves:
- Reducing to canonical forms with minimal element 0 and coprime coordinates
- Using periodic colourings that repeat with some period `q`
- Verifying that these periodic colourings satisfy the polychromatic property using bit vector
  operations

The main theorem states:

```anchor final (module := Polychromatic.Main)
theorem final_result (S : Finset ℤ) (hS : S.card = 4) :
    HasPolychromColouring (Fin 3) S := by
  sorry
```

This proof is currently incomplete, pending the integration of the computational and theoretical
components.

# Compactness and Rado's Selection Principle

A key technical tool in extending finite colourings to infinite ones is Rado's selection principle.
This principle states: given functions `g : Finset α → α → β` where `β` is finite, there exists a
single function `χ : α → β` which is constructed from `g`. More precisely, for each finite set `s`,
there exists a larger set `t ⊇ s` such that `χ` and `g t` agree on `s`.

This allows us to construct infinite colourings from a family of finite ones by a compactness
argument using Tychonoff's theorem.

As an application, we formalise the de Bruijn–Erdős theorem: if every finite subgraph of a graph `G`
is `k`-colourable, then `G` is `k`-colourable.

# Repository Structure

The repository structure is as follows:
: `Generation`

  C++, Python and Z3 code which generates explicit colourings for certain sets. The C++ program
  searches for periodic colourings and outputs them in a format suitable for verification.

: `Lean`

  Lean 4 formal proofs of the results. This includes:
  - Core definitions (`Colouring.lean`)
  - The Lovász Local Lemma (`LocalLemma.lean`)
  - Existence proofs via probabilistic methods (`Existence.lean`)
  - The polychromatic number and its properties (`PolychromNumber.lean`)
  - The Strauss function (`LovaszFunction.lean`)
  - Compactness and Rado's selection principle (`Compactness.lean`)
  - The four-three problem (`FourThree/`)
  - The main theorem (`Main.lean`)

: `Verso`

  Lean code to generate the website documentation using the Verso literate programming framework.

: `site`

  A partial Jekyll website, which is completed by the code in `Verso` to produce the final
  documentation.
