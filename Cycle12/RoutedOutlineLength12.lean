import Cycle12.RoutedOutlineWalk12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem visitChain_exact_length {u v : V} (q : VisitChain G u v) :
    q.walk.length+1=(q.visits.map (fun p => p.walk.length)).sum+q.visits.length := by
  induction q with
  | single p => simp [VisitChain.walk,VisitChain.visits]
  | cons p h q ih =>
    simp only [VisitChain.walk,VisitChain.visits,Walk.length_append,Walk.length_cons,
      List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem outlineVisits_length_sum (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    (∑ z∈c.cycle.dropLast.support.toFinset,(outlineVisits c route z).length)=
      ∑ z,(route z).length := by
  let S := c.cycle.dropLast.support.toFinset
  let T := S.filter (fun z => c.start z≠c.finish z)
  have hst : (∑ z∈S,(outlineVisits c route z).length)=
      ∑ z∈T,(outlineVisits c route z).length := by
    apply (Finset.sum_subset (filter_subset _ _) ?_).symm
    intro z hz hzt
    have hn : ¬(z∈c.cycle.dropLast.support ∧ c.start z≠c.finish z) := by
      intro hh
      exact hzt (mem_filter.mpr ⟨List.mem_toFinset.mpr hh.1,hh.2⟩)
    exact Walk.length_eq_zero_iff.mpr (outlineVisits_nil c route z hn)
  rw [hst,Finset.sum_subtype T (p:=fun z => z∈c.cycle.dropLast.support ∧
      c.start z≠c.finish z) (fun z => by simp only [T,S,mem_filter,List.mem_toFinset])]
  exact Finset.sum_congr rfl (fun z _ => congrArg Walk.length (outlineVisits_switch c route z))

theorem outlineClosedWalk_length (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z)) :
    (outlineClosedWalk c route).length=c.cycle.length+∑ z,(route z).length := by
  have hh := visitChain_exact_length (outlineChain c route)
  rw [outlineChain,VisitChain.of_walk_visits,List.map_map] at hh
  simp only [Function.comp_def,List.length_map,Walk.length_support,Walk.length_dropLast] at hh
  rw [←List.sum_toFinset (fun z => (outlineVisits c route z).length)
    c.isCycle.isPath_dropLast.support_nodup,outlineVisits_length_sum] at hh
  change (outlineChain c route).walk.length+1 = _ at hh
  have hpos := c.isCycle.three_le_length
  simp only [outlineClosedWalk,Walk.length_cons]
  omega

/-- The extra port at every switched vertex exactly cancels the unit
removed when an internal vertex count is converted into a route length. -/
theorem outlineClosedWalk_length_interiors (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hp : ∀ z,(route z).IsPath) :
    (outlineClosedWalk c route).length=c.vertices.card+∑ z,(routeInterior (route z)).card := by
  have he (z : c.Switch) := routeInterior_path_card (route z) (hp z) z.property.2
  rw [outlineClosedWalk_length,outline_ports_card]
  simp_rw [←he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  omega

end
end Cycle12
