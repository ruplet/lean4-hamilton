import Lean

import HamiltonToItauto.Basic
import HamiltonToItauto.Formula

open Lean Lean.Meta

def getTypeStr (var : Lean.MVarId): MetaM String := do
  let varType <- var.getType
  return varType.toString

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  ipc_formula.withContext do
    let ipc_type <- ipc_formula.getType
    IO.println s!"Formula: {ipc_type}"
