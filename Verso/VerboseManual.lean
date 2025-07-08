/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot
-/

import Berso.BersoBlog

-- import VerboseManual.TacticReference

-- This gets access to most of the manual genre
open Verso.Genre Blog

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Code.External

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../lean"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Polychromatic"

#doc (Page) "Verbose Lean" =>

# Overview

The first main goal is to train students to have a clear view of the

# Examples

```anchor IsPolychrom (module := Polychromatic.Basic)
def IsPolychrom (S : Set G) (χ : G → K) : Prop :=
  ∀ n : G, ∀ k, ∃ i ∈ n +ᵥ S, χ i = k
```

Here is a term

```anchorTerm IsPolychrom (module := Polychromatic.Basic)
n +ᵥ S
```

and then the end
