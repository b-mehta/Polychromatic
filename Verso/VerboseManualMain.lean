/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import Berso.BersoBlog
import VerboseManual
import VerboseManual.TestPage

open Verso Doc
open Verso.Genre Blog Site Syntax

open Std (HashMap)

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <body>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

def mySite : Site := site VerboseManual /
  "test" VerboseManual.TestPage

def main := blogMain theme mySite (options := ["--output", "../site"])

#eval main
