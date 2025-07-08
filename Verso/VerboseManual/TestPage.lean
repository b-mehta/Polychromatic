/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot
-/

import Berso.BersoBlog

-- import VerboseManual.TacticReference

-- This gets access to most of the blog genre
open Verso.Genre Blog

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Code.External

-- open VerboseManual

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../lean"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Polychromatic"

#doc (Page) "Test page" =>

# Overview

asdfsdf
