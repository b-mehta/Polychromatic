/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Berso.BersoBlog

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
set_option verso.exampleModule "Polychromatic"

#doc (Page) "Polychromatic Colourings" =>

# Overview

This repository aims to formalise results related to polychromatic colourings of integers. Given a
finite set $`S` of integers, a colouring of the integers is called `S`-polychromatic if every
translate of `S` contains an element of each colour class.
A primary target is to show that for any set `S` of size 4, there is an `S`-polychromatic colouring
in 3 colours.

The repository structure is as follows:
- `Generation`: Contains C++, Python and Z3 code which generates explicit colourings for given sets
- `Lean`: Contains Lean formal proofs of the results
- `Verso`: Contains Lean code to generate the website
- `site`: Contains a template Jekyll website, which is filled in by `Verso`-enabled code in CI

# Examples

```anchor my_IsPolychrom (module := Polychromatic.Basic)
def IsPolychrom (S : Set G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ i ∈ n +ᵥ S, χ i = k
```

Here is a term
```anchorTerm my_IsPolychrom (module := Polychromatic.Basic)
n +ᵥ S
```

```leanInit demo
-- This block initializes a Lean context
```

and here is another test
```lean demo
example := if True then 1 else 0
```
