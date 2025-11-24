/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Berso.Main

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

Then, we define the polychromatic number of {anchorTerm final}`S` to be the maximum number of
colours possible in an {anchorTerm final}`S`-polychromatic colouring.

A primary target is to show that for any set {anchorTerm final}`S` of size {anchorTerm final}`4`,
there is an {anchorTerm final}`S`-polychromatic colouring in {anchorTerm final}`3` colours.

The repository structure is as follows:
: `Generation`

  C++, Python and Z3 code which generates explicit colourings for certain sets

: `Lean`

  Lean formal proofs of the results
: `Verso`

  Lean code to generate the website
: `site`

  A partial Jekyll website, which is completed by the code in `Verso`

# Examples

```anchor IsPolychrom (module := Polychromatic.Colouring)
def IsPolychrom (S : Finset G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k : K, ∃ a ∈ S, χ (n + a) = k
```

asdf
