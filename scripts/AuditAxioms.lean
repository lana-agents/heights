import Heights
import Solution
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter.PrivateModule

/-!
# Public-declaration logical-dependency audit

The compiled-module manifest and the environment walk select declarations by
independent mechanisms. Their outputs are compared by `audit_axioms.sh` before
this file checks every selected declaration. P1 may legitimately select zero
names: `Heights.lean` contains only an anonymous link-check example and
`Comparator.Solution` exports nothing. The set starts growing in P2.
-/

open Lean Elab Command

private def auditedRoots : List Name :=
  [`Heights, `Solution]

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def inAuditedRoot (moduleName : Name) : Bool :=
  auditedRoots.any fun root => moduleName == root || root.isPrefixOf moduleName

private def isAuditedPublicName (env : Environment) (declName : Name) : Bool :=
  !isPrivateName declName && !isReservedName env declName

private def visitedDeclarations : CoreM (Array Name) := do
  let env ← getEnv
  env.constants.foldM (init := #[]) fun names declName _ => do
    let some moduleName ← findModuleOf? declName | return names
    if inAuditedRoot moduleName && isAuditedPublicName env declName then
      return names.push declName
    return names

private def compiledManifest : CoreM (Array Name) := do
  let env ← getEnv
  let mut names := #[]
  for h : moduleIdx in *...env.header.moduleNames.size do
    let moduleName := env.header.moduleNames[moduleIdx]
    if inAuditedRoot moduleName then
      for declName in env.header.moduleData[moduleIdx]!.constNames do
        if isAuditedPublicName env declName then
          names := names.push declName
  return names

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

private def renderNames (names : Array Name) : String :=
  String.intercalate "\n" ((sortNames names).toList.map Name.toString) ++
    (if names.isEmpty then "" else "\n")

private def writeNames (names : Array Name) : CommandElabM Unit := do
  let some output ← IO.getEnv "HEIGHTS_AUDIT_OUTPUT" |
    throwError "HEIGHTS_AUDIT_OUTPUT is required in manifest modes"
  IO.FS.writeFile output (renderNames names)

run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `Challenge then
    throwError "Challenge leaked into the audited Solution environment"
  let mode ← IO.getEnv "HEIGHTS_AUDIT_MODE"
  match mode with
  | some "manifest" =>
      writeNames (← liftCoreM compiledManifest)
  | some "visited" =>
      writeNames (← liftCoreM visitedDeclarations)
  | _ => liftCoreM do
      let declarations := sortNames (← visitedDeclarations)
      let mut violations : Array (Name × Array Name) := #[]
      for declName in declarations do
        let dependencies := sortNames (← collectAxioms declName)
        IO.println s!"AXIOM_AUDIT|DECL|{declName}|{String.intercalate ","
          (dependencies.toList.map Name.toString)}"
        let forbidden := dependencies.filter fun name => !allowedAxioms.contains name
        unless forbidden.isEmpty do
          violations := violations.push (declName, forbidden)
      unless violations.isEmpty do
        let messages := violations.toList.map fun (declName, dependencies) =>
          s!"{declName}: {String.intercalate ", "
            (dependencies.toList.map Name.toString)}"
        throwError "disallowed transitive axioms:\n{String.intercalate "\n" messages}"
      IO.println s!"AXIOM_AUDIT|SUMMARY|{declarations.size}"
