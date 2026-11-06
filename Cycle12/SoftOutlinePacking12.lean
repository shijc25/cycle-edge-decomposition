import Cycle12.RoutedOutlineTrail12
import Cycle12.Foundations.SoftIntersectionBudget

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A routed quotient cycle decomposes into one cycle plus its actual
soft intersections. There is no additive charge per routing demand. -/
theorem soft_outline_packing (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hp : ∀ z,(route z).IsPath)
    (hd : Pairwise (fun z w => Disjoint (route z).edgeSet (route w).edgeSet))
    (ho : ∀ z,Disjoint c.edges (route z).edgeSet)
    (hi : Pairwise (fun z w => Disjoint (routeInterior (route z)) (routeInterior (route w)))) :
    ∃ P : CyclePacking G, P.used=c.edges∪(⋃ z,(route z).edgeSet) ∧
      P.count≤1+∑ z,(routeInterior (route z)∩c.vertices).card := by
  obtain ⟨P,hP,hcount⟩ := soft_closed_trail_count (outlineClosedWalk c route)
    (outlineClosedWalk_isTrail c route hp hd ho) c.vertices
    (fun z => routeInterior (route z)) hi (outlineClosedWalk_support c route)
    (outlineClosedWalk_length_interiors c route hp)
  exact ⟨P,hP.trans (outlineClosedWalk_edges c route),hcount⟩

theorem soft_outline_packing_with_budget (c : CycleOutline G)
    (route : ∀ z : c.Switch, G.Walk (c.start z) (c.finish z))
    (hp : ∀ z,(route z).IsPath)
    (hd : Pairwise (fun z w => Disjoint (route z).edgeSet (route w).edgeSet))
    (ho : ∀ z,Disjoint c.edges (route z).edgeSet)
    (hi : Pairwise (fun z w => Disjoint (routeInterior (route z)) (routeInterior (route w))))
    (fee : c.Switch → ℝ)
    (hfee : ∀ z,((routeInterior (route z)∩c.vertices).card:ℝ)≤fee z) :
    ∃ P : CyclePacking G, P.used=c.edges∪(⋃ z,(route z).edgeSet) ∧
      (P.count:ℝ)≤1+∑ z,fee z := by
  obtain ⟨P,hP,hcount⟩ := soft_outline_packing c route hp hd ho hi
  refine ⟨P,hP,?_⟩
  have hc : (P.count:ℝ)≤1+∑ z,((routeInterior (route z)∩c.vertices).card:ℝ) := by
    exact_mod_cast hcount
  exact hc.trans (add_le_add (le_refl 1) (Finset.sum_le_sum (fun z _ => hfee z)))

end
end Cycle12
