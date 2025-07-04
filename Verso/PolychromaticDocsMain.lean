/-
Copyright (c) Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Std.Data.HashMap
import VersoManual
import PolychromaticDocs

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open VerboseManual

def config : Config where
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 2

def main := manualMain (%doc VerboseManual) (config := config.addKaTeX)
