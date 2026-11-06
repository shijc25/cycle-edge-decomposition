import Cycle12.Foundations.PackingEmbedding
import Cycle12.Foundations.ReservoirLift

/-! Exact edge ownership and integer-weight accounting for the infinite
vertex-removal reductions of the small-circumference terminal theorem. -/
namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 2000000

theorem indexed_packing_cost_mapEmbedding {W : Type} [Fintype W]
    {G : SimpleGraph V} (P : Cycle13.CyclePacking G) (f : V ↪ W) :
    (P.mapEmbedding f).cost=P.cost := by
  unfold Cycle13.CyclePacking.cost
  rw [Cycle13.CyclePacking.singles_mapEmbedding]
  rfl

theorem combine_with_edge_complement {G H : SimpleGraph V} (hHG : H ≤ G)
    (P : Cycle13.CyclePacking H) (Q : Cycle13.CyclePacking (G.deleteEdges H.edgeSet)) :
    ∃ C : Cycle13.CyclePacking G, C.cost=P.cost+Q.cost := by
  have hd : Disjoint H.edgeSet (G.deleteEdges H.edgeSet).edgeSet := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  have hrest : G.edgeSet\(H.edgeSet∪(G.deleteEdges H.edgeSet).edgeSet)=∅ := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_eq_empty.mpr (by intro e he; by_cases h : e ∈ H.edgeSet <;> simp_all)
  let C := P.combine Q hHG (G.deleteEdges_le H.edgeSet) hd
  refine ⟨C,?_⟩
  unfold Cycle13.CyclePacking.cost C
  rw [Cycle13.CyclePacking.combine_count,Cycle13.CyclePacking.combine_singles,hrest,
    Set.ncard_empty]
  ring

def incidentRemainder (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  G.deleteEdges (reservoirLift S (G.induce (S:Set V))).edgeSet

theorem induced_incident_edge_partition (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S:Set V)).edgeSet.ncard+(incidentRemainder G S).edgeSet.ncard=G.edgeSet.ncard := by
  let H := reservoirLift S (G.induce (S:Set V))
  have hsub : H.edgeSet ⊆ G.edgeSet := SimpleGraph.edgeSet_mono (reservoirLift_le G S _ le_rfl)
  have hh := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
  have heq : H.edgeSet.ncard=(G.induce (S:Set V)).edgeSet.ncard := by
    dsimp [H,reservoirLift]
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding S).sym2Map.injective]
  rw [heq] at hh
  unfold incidentRemainder
  rw [SimpleGraph.edgeSet_deleteEdges]
  change (G.edgeSet\H.edgeSet).ncard+(G.induce (S:Set V)).edgeSet.ncard=G.edgeSet.ncard at hh
  exact Nat.add_comm _ _ |>.trans hh

/-- Remove vertices outside the nonempty retained set S, paying exactly for
all their incident edges, and extend a predecessor-rank terminal certificate.
No structural classification is assumed in this compositional lemma. -/
theorem terminal_affine_vertex_reduction (G : SimpleGraph V) (S : Finset V)
    (hS : S.Nonempty)
    (P : Cycle13.CyclePacking (G.induce (S:Set V)))
    (hP : P.cost ≤ 19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard)
    (Q : Cycle13.CyclePacking (incidentRemainder G S))
    (hQ : Q.cost ≤ 19*(Fintype.card V-S.card)+6*(incidentRemainder G S).edgeSet.ncard) :
    ∃ C : Cycle13.CyclePacking G, C.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let P' := P.mapEmbedding (reservoirEmbedding S)
  have hHG := reservoirLift_le G S (G.induce (S:Set V)) le_rfl
  obtain ⟨C,hC⟩ := combine_with_edge_complement hHG P' Q
  have hcost : P'.cost=P.cost := indexed_packing_cost_mapEmbedding P _
  have he := induced_incident_edge_partition G S
  have hsize := Finset.card_le_univ S
  have hnonempty := hS.card_pos
  refine ⟨C,?_⟩
  calc
    C.cost=P.cost+Q.cost := by
      calc
        C.cost=P'.cost+Q.cost := hC
        _=P.cost+Q.cost := congrArg (fun t => t+Q.cost) hcost
    _ ≤ (19*(S.card-1)+6*(G.induce (S:Set V)).edgeSet.ncard)+
        (19*(Fintype.card V-S.card)+6*(incidentRemainder G S).edgeSet.ncard) :=
      Nat.add_le_add hP hQ
    _ = _ := by omega

end
end Cycle12
