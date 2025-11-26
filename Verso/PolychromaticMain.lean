/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/

import Berso.Main
import PolychromaticSite

open Verso Genre Blog Site Syntax

open Output Html Template in
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

def jekyllHeader : String :=
"---
layout: default
useverso: true
---"


def mySite : Site := site PolychromaticSite -- /
  -- "test" PolychromaticSite.Main

def baseUrl := "{{ site.baseurl }}/docs/"

def linkTargets : Code.LinkTargets TraverseContext where
  const name _ :=
    #[{ shortDescription := "doc"
        description := s!"Documentation for {name}"
        href := s!"{baseUrl}find/?pattern={name}#doc"}]
  definition name _ :=
    #[{ shortDescription := "def"
        description := s!"Definition for {name}"
        href := s!"{baseUrl}find/?pattern={name}#doc"}]
  keyword name _ :=
    #[{ shortDescription := "keyword"
        description := s!"Declaration for {name}"
        href := s!"{baseUrl}find/?pattern={name}#doc"}]

def main : IO UInt32 :=
  Berso.blogMain theme mySite
    (options := ["--output", "../site/_pages"])
    (linkTargets := linkTargets)
    (header := jekyllHeader)

run_meta
  let opt ← Lean.getOptions
  if Lean.Elab.inServer.get opt then
    _ ← main
