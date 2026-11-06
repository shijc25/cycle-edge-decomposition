import Cycle12.Foundations.FiniteGraphJanson
import Cycle12.BernoulliHarris
import Cycle12.Independent.ErdosGallai

open Lean Elab Command

#print axioms Cycle13.vertex_sample_edge_lower_tail
#print axioms Cycle13.finite_graph_janson_restricted
#print axioms Cycle12.bernoulli_harris_monotone
#print axioms Cycle12.Independent.erdosGallai_cycle

set_option maxHeartbeats 0
set_option maxRecDepth 10000

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[`Cycle13.vertex_sample_edge_lower_tail,
    `Cycle13.finite_graph_janson_restricted, `Cycle12.bernoulli_harris_monotone,
    `Cycle12.Independent.erdosGallai_cycle]
  for root in roots do
    let mut todo := #[root]
    let mut seen : NameHashSet := {}
    let mut modules : Std.HashSet String := {}
    let mut axioms : Array Name := #[]
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some ci := env.checked.get.find? name | throwError "Missing body: {name}"
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial dependency: {name}"
      if let .axiomInfo _ := ci then
        unless #[`propext, `Classical.choice, `Quot.sound].contains name do
          throwError "Unaccepted axiom: {name}"
        axioms := axioms.push name
      if let some idx := env.getModuleIdxFor? name then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if mod.startsWith "ErdosProblems" || mod.startsWith "ProbMethodCombinatorics" then
          throwError "Excluded dependency remains: {name} in {mod}"
        modules := modules.insert mod
      for dep in ci.getUsedConstantsAsSet do todo := todo.push dep
      if let .inductInfo info := ci then
        for dep in info.all do todo := todo.push dep
      if let .quotInfo _ := ci then todo := todo.push `Eq
    logInfo m!"REPLACEMENT AUDIT PASS {root}: {seen.size} declarations, {modules.size} modules, axioms {axioms}"
