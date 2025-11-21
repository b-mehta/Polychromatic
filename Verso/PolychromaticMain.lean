/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Std.Data.HashMap
import Berso.Main
-- import PolychromaticSite.Main
import PolychromaticSite

open Verso Doc
open Verso.Genre Blog Site Syntax

open Std (HashMap)

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <body>
        <div class="main" role="main">
          <div class="wrap">
            {{ (← param "content") }}
          </div>
        </div>
      </body>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

def jekyllHeader : String :=
"---
layout: default
useverso: true
---"


def mySite : Site := site PolychromaticSite -- /
  -- "test" PolychromaticSite.Main

def main : IO UInt32 :=
  Berso.blogMain theme mySite
    (options := ["--output", "../site/_pages"])
    (header := jekyllHeader)

run_meta
  let opt ← Lean.getOptions
  if Lean.Elab.inServer.get opt then
    _ ← main
