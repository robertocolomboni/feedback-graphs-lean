import Tournament
import Lean

-- Omitting a `module` header includes private declarations from transitive imports.
-- Tournament imports every project module.
open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_elab do
  let env := (← getEnv).setExporting false
  let declarations := env.checked.get.constants.fold (init := #[]) fun acc name ci =>
    let owner := env.getModuleIdxFor? name |>.bind (env.header.moduleNames[·]?)
    if owner.any (fun m => m == `Tournament || "Tournament.".isPrefixOf m.toString)
    then acc.push (name, ci) else acc
  if declarations.isEmpty then
    throwError "FAIL: no project declarations found"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut used : NameSet := {}
  for (name, ci) in declarations do
    if ci.isAxiom then
      throwError "FAIL: project axiom {name}"
    if ci.isUnsafe then
      throwError "FAIL: unsafe project declaration {name}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless ci.hasValue (allowOpaque := true) do
        throwError "FAIL: missing body for {name}"
    | _ => pure ()
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "FAIL: {name} depends on forbidden axiom {axiomName}"
      used := used.insert axiomName
  logInfo m!"PASS: {declarations.size} project declarations checked; no project axioms, unsafe declarations or forbidden axiom dependencies."
  logInfo m!"Transitive axioms used: {used.toArray.qsort Name.lt}"
