import Cycle12.Coefficient12Complete
import Lean.Replay

open Lean Elab Command

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient_primitive"

/-- Independently expose the intended edge-partition statement, including
the exact component count and the absence of any additional graph hypothesis. -/
example : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ (k : ℕ)
    (parts : Fin k → Set (Sym2 (Fin n))),
    (∀ j, (∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ parts j = p.edgeSet) ∨
      ∃ e ∈ G.edgeSet, parts j = {e}) ∧
    Pairwise (fun j l => Disjoint (parts j) (parts l)) ∧
    (⋃ j, parts j) = G.edgeSet ∧
    Nat.le k (Nat.mul 12 (Nat.sub n (Nat.card G.ConnectedComponent))) := by
  intro n G
  obtain ⟨k, ⟨parts, hp, hd, hu⟩, hk⟩ := Cycle12.coefficient12 n G
  exact ⟨k, parts, hp, hd, hu, hk⟩

#print axioms Cycle12.coefficient12
#print Cycle13.CycleOrSingleEdge
#print Cycle13.EdgeDecomposition
#print Cycle13.componentCount
#check SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length

set_option maxRecDepth 10000
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let localFile ← liftIO <| IO.FS.readFile "audit/local-modules.txt"
  let locals : Std.HashSet String := .ofList (localFile.splitOn "\n")
  let allProjectKinds : Std.HashMap String Nat :=
    env.checked.get.constants.fold (init := {}) fun acc name ci =>
      match env.getModuleIdxFor? name with
      | some idx =>
        if locals.contains moduleNames[idx.toNat]!.toString then
          let kind := declarationKind ci
          acc.insert kind (acc.getD kind 0 + 1)
        else acc
      | none => acc
  let allProjectTotal := allProjectKinds.toList.foldl (fun n entry => n + entry.2) 0
  let declaredLocalAxioms : Array String := env.checked.get.constants.fold (init := #[]) fun acc name ci =>
    match ci, env.getModuleIdxFor? name with
    | .axiomInfo _, some idx =>
      if locals.contains moduleNames[idx.toNat]!.toString then acc.push name.toString else acc
    | _, _ => acc
  unless declaredLocalAxioms.isEmpty do
    throwError "The retained project modules declare axioms: {declaredLocalAxioms}"
  let mut todo : Array Name := #[`Cycle12.coefficient12]
  let mut seen : NameHashSet := {}
  let mut table : Std.HashMap Name ConstantInfo := {}
  let mut rows : Array Json := #[]
  let mut axioms : Array String := #[]
  let mut localAxioms : Array String := #[]
  let mut unsafeNames : Array String := #[]
  let mut localTotal : Nat := 0
  let mut localTheorems : Nat := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.checked.get.find? name
      | throwError "Cannot inspect the actual declaration body of {name}"
    table := table.insert name ci
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => moduleNames[idx.toNat]!.toString
      | none => env.mainModule.toString
    if moduleName.startsWith "ErdosProblems" || moduleName.startsWith "ProbMethodCombinatorics" then
      throwError "Removed library appears in the main proof: {moduleName} ({name})"
    let localDecl := locals.contains moduleName
    if localDecl then
      localTotal := localTotal + 1
      if ci.isTheorem then localTheorems := localTheorems + 1
    if ci.isUnsafe || ci.isPartial then unsafeNames := unsafeNames.push name.toString
    if let .axiomInfo _ := ci then
      axioms := axioms.push name.toString
      if localDecl then localAxioms := localAxioms.push name.toString
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName),
      ("kind", toJson (declarationKind ci)), ("project_local", toJson localDecl)]
    for dep in ci.getUsedConstantsAsSet do
      todo := todo.push dep
    if let .inductInfo v := ci then
      for dep in v.all do todo := todo.push dep
    if let .quotInfo _ := ci then
      todo := todo.push `Eq
    if rows.size % 5000 == 0 then
      liftIO <| IO.FS.writeFile "audit/inspection-progress.json"
        (Json.mkObj [("declarations", toJson rows.size), ("current", toJson name.toString),
          ("project_declarations", toJson localTotal)]).compress
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  unless axioms.all allowed.contains && localAxioms.isEmpty && unsafeNames.isEmpty do
    throwError "Unexpected axioms/unsafe declarations: {axioms}; {localAxioms}; {unsafeNames}"
  unless localTotal ≤ allProjectTotal do
    throwError "The main-dependency declaration count exceeds the retained-module count"
  let report := Json.mkObj [
    ("entry", toJson "Cycle12.coefficient12"),
    ("uncached_body_traversal", toJson true),
    ("all_declaration_bodies_found", toJson true),
    ("removed_libraries_checked_absent", toJson true),
    ("transitive_declarations", toJson rows.size),
    ("project_declarations", toJson localTotal),
    ("project_theorems", toJson localTheorems),
    ("all_retained_project_declarations", toJson allProjectTotal),
    ("all_retained_project_kind_counts", Json.mkObj
      (allProjectKinds.toList.map fun (kind, count) => (kind, toJson count))),
    ("axioms", toJson axioms), ("new_project_axioms", toJson localAxioms),
    ("new_project_axiom_count", toJson localAxioms.size),
    ("declared_project_axioms_in_all_retained_modules", toJson declaredLocalAxioms),
    ("unsafe_or_partial_dependencies", toJson unsafeNames),
    ("declarations", Json.arr rows)]
  let reportPath ← liftIO <| IO.getEnv "CYCLE12_AUDIT_REPORT"
  let path := reportPath.getD "audit/main-dependency-audit.json"
  liftIO <| IO.FS.writeFile path report.pretty
  logInfo m!"Direct proof-body audit: {rows.size} declarations; {localTotal} project declarations; {localTheorems} project theorems; {localAxioms.size} new axioms."
  if (← liftIO <| IO.getEnv "CYCLE12_FRESH_REPLAY") == some "1" then
    let empty ← liftIO <| mkEmptyEnvironment
    let checked ← liftIO <| empty.toKernelEnv.replay table
    let some result := checked.find? `Cycle12.coefficient12
      | throwError "The kernel replay did not produce the target theorem"
    unless result.type == (env.find? `Cycle12.coefficient12).get!.type do
      throwError "The kernel-replayed statement changed"
    liftIO <| IO.FS.writeFile (path ++ ".kernel-replay.json")
      (Json.mkObj [("passed", toJson true), ("initial_environment", toJson "empty"),
        ("entry", toJson "Cycle12.coefficient12"), ("declarations", toJson table.size),
        ("axioms", toJson axioms)]).pretty
    logInfo "The main theorem and its actual dependency declarations passed kernel replay into an empty environment."
