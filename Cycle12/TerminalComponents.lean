import Cycle12.TerminalReduction
import Cycle12.TerminalNoFourCycle
import Cycle12.Foundations.Components

namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

/-- Assemble weighted terminal bounds over every component, including
isolated vertices, obtaining the exact n-c(G) term. -/
theorem terminal_affine_from_components (G : SimpleGraph V)
    (hcomp : ∀ c : G.ConnectedComponent, ∃ P : Cycle13.CyclePacking c.toSimpleGraph,
      P.cost ≤ 19*(Fintype.card c-1)+6*c.toSimpleGraph.edgeSet.ncard) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  choose P hP using hcomp
  let f := fun c : G.ConnectedComponent => (Function.Embedding.subtype (·∈c))
  let H := fun c : G.ConnectedComponent => c.toSimpleGraph.map (f c)
  let Q := fun c : G.ConnectedComponent => (P c).mapEmbedding (f c)
  have hle : ∀ c, H c ≤ G := by
    intro c u v h
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj (f c) c.toSimpleGraph u v).mp h
    exact c.toSimpleGraph_hom.map_adj hab
  have hd : Pairwise (fun c d => Disjoint (H c).edgeSet (H d).edgeSet) := by
    intro c d hcd
    simp only [H,SimpleGraph.edgeSet_map]
    exact component_edges_disjoint G hcd
  have hu : (⋃ c, (H c).edgeSet)=G.edgeSet := by
    simp only [H,SimpleGraph.edgeSet_map]
    exact component_edges_cover G
  let C := Cycle13.CyclePacking.assemble H hle hd Q
  have hcost : C.cost=∑ c, (P c).cost := by
    dsimp only [C]
    erw [Cycle13.CyclePacking.assemble_cost H hle hd hu Q]
    apply Finset.sum_congr rfl
    intro c _
    exact indexed_packing_cost_mapEmbedding (P c) (f c)
  have hm : (∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeSet.ncard)=G.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard] using sum_component_edges G
  refine ⟨C,?_⟩
  calc
    C.cost=∑ c, (P c).cost := hcost
    _ ≤ ∑ c : G.ConnectedComponent, (19*(Fintype.card c-1)+6*c.toSimpleGraph.edgeSet.ncard) :=
      Finset.sum_le_sum (fun c _ => hP c)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,sum_component_ranks,hm]

/-- Closed rank form of the no-four-cycle terminal case for every finite
graph. No connectedness or nonempty-vertex hypothesis is needed. -/
theorem terminal_rank_no_four_cycle (G : SimpleGraph V)
    (hshort : Cycle13.NoCycleAtLeast G 4) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_components G
  intro c
  have : Nonempty c := c.connected_toSimpleGraph.nonempty
  have hc : Cycle13.NoCycleAtLeast c.toSimpleGraph 4 := by
    intro v p hp
    have hh := hshort v.val (p.map c.toSimpleGraph_hom) (hp.map Subtype.val_injective)
    erw [Walk.length_map] at hh
    exact hh
  exact terminal_affine_no_four_cycle c.toSimpleGraph hc

end
end Cycle12
