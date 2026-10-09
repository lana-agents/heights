/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import HeightsBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc HeightsBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
