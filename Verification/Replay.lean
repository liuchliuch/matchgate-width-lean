/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the Lean LICENSE.
Authors: Kim Morrison, Sebastian Ullrich

The exact-module replay function below follows pinned Lean 4.34.1
src/lean/LeanChecker.lean (replayFromImports). Unlike leanchecker's CLI prefix
selection, this driver replays precisely the enumerated modules, sequentially.
This is the same Lean kernel, not an independent external verifier.
-/
import Lean.CoreM
import Lean.Replay

open Lean

unsafe def replayExact (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"Missing artifact for {module}: {mFile}"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  discard <| env.toKernelEnv.replay newConstants
  env.freeRegions

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  unless !args.isEmpty do throw <| IO.userError "No delivered modules supplied"
  for arg in args do
    let mod := (arg.splitOn ".").foldl Name.str Name.anonymous
    replayExact mod
    IO.println s!"REPLAY_OK {mod.toString false}"
    (← IO.getStdout).flush
  IO.println s!"REPLAY_SUMMARY {args.length}"
  return 0
