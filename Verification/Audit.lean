import MatchgateWidth
import PaperProofs
import Verification
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit declarations by originating module, including private helpers. -/
open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let mut checked : Nat := 0
  let mut modules : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if mod == `MatchgateWidth || mod.toString.startsWith "MatchgateWidth." ||
          mod == `PaperStatements || mod == `PaperProofs || mod == `Verification ||
          mod == `Verification.Regression || mod == `Verification.OrderRegression then
        if info.isAxiom then
          throwError "Project axiom: {mod}: {name}"
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Unapproved axiom {ax} used by {mod}: {name}"
        checked := checked + 1
        if !modules.contains mod then modules := modules.push mod
  unless checked > 0 do throwError "No project declarations audited"
  logInfo m!"AUDIT_OK declarations={checked} modules_with_declarations={modules.size}"
