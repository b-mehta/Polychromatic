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
size at least `m` has a polychromatic `k`-colouring.


The repository structure is as follows:
: `Generation`

  C++, Python and Z3 code which generates explicit colourings for certain sets

: `Lean`

  Lean formal proofs of the results
: `Verso`

  Lean code to generate the website
: `site`

  A partial Jekyll website, which is completed by the code in `Verso`
