import Cycle12.StarComponents
import Cycle12.TwinReduction

namespace Cycle12
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The endpoints of a two-edge exterior path are actual degree-two twins
in the whole graph, not merely in the induced exterior graph. -/
theorem six_cycle_external_two_path_twins (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z) :
    ∃ a∈c.support, (∀ v, G.Adj x v ↔ v=a ∨ v=y) ∧
      (∀ v, G.Adj z v ↔ v=a ∨ v=y) := by
  obtain ⟨a,ha,hX,hZ⟩ := six_cycle_external_two_path_unique_attachment
    G hconn hrobust c hc hlen hshort hx hy hz hn hxy hyz
  obtain ⟨hL,hR⟩ := six_cycle_external_two_path_endpoints_are_leaves
    G hconn hrobust c hc hlen hshort hx hy hz hn hxy hyz
  refine ⟨a,ha,?_,?_⟩
  · intro v
    constructor
    · intro hv
      by_cases hvc : v∈c.support
      · exact Or.inl ((hX v hvc).mp hv)
      · exact Or.inr (hL v hvc hv)
    · rintro (rfl | rfl)
      · exact (hX _ ha).mpr rfl
      · exact hxy
  · intro v
    constructor
    · intro hv
      by_cases hvc : v∈c.support
      · exact Or.inl ((hZ v hvc).mp hv)
      · exact Or.inr (hR v hvc hv)
    · rintro (rfl | rfl)
      · exact (hZ _ ha).mpr rfl
      · exact hyz.symm

noncomputable section
attribute [local instance] Classical.propDecidable

/-- This reduction consumes an actual smaller-graph packing and restores
all four deleted edges as a four-cycle. -/
theorem terminal_delete_six_cycle_two_path (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (P : Cycle13.CyclePacking (G.induce ((({x,z}:Finset V)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((({x,z}:Finset V)ᶜ).card-1)+
      6*(G.induce ((({x,z}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G,
      Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  obtain ⟨a,ha,hX,hZ⟩ := six_cycle_external_two_path_twins
    G hconn hrobust c hc hlen hshort hx hy hz hn hxy hyz
  have hax : a≠x := fun he => hx (he ▸ ha)
  have hay : a≠y := fun he => hy (he ▸ ha)
  have haz : a≠z := fun he => hz (he ▸ ha)
  have hxz : x≠z := by
    have hh := (List.nodup_cons.mp hn).1
    intro he
    exact hh (by simp [he])
  exact terminal_delete_degree_two_twins G a y x z hay hxz hax haz
    hxy.ne.symm hyz.ne hX hZ P hP

end
end Cycle12
