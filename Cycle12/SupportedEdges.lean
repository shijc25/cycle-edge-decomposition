import Cycle12.Foundations.DFSPartition
import Cycle12.Foundations.MixedGraphCoordinates
import OAI.Combinatorics.CycleDecomposition.ScaleExtraction

namespace Cycle12
open Real Finset SimpleGraph Cycle13
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem supported_edge_count_le_square (G : SimpleGraph V) (A : Finset V)
    (hG : SupportedOn G A) : (edgeCount G:ℝ) ≤ (A.card:ℝ)^2/2 := by
  have he : reservoirLift A (G.induce (A:Set V))=G := by
    rw [reservoirLift_induce]
    ext x y
    exact ⟨fun h => h.1,fun h => ⟨h,hG h⟩⟩
  have hcount : (G.induce (A:Set V)).edgeSet.ncard=G.edgeSet.ncard := by
    calc
      _ = (reservoirLift A (G.induce (A:Set V))).edgeSet.ncard := by
        rw [reservoirLift,SimpleGraph.edgeSet_map,
          Set.ncard_image_of_injective _ (reservoirEmbedding A).sym2Map.injective]
        rfl
      _ = G.edgeSet.ncard := congrArg (fun H : SimpleGraph V => H.edgeSet.ncard) he
  have hh := Cycle13.MixedSample.twice_graph_edges_le_order_sq (G.induce (A:Set V))
  simp only [Set.fintypeCard_eq_ncard,Set.ncard_coe_finset] at hh
  rw [hcount] at hh
  have hn : edgeCount G=G.edgeSet.ncard := by
    simp only [edgeCount,SimpleGraph.edgeFinset,Set.ncard_eq_toFinset_card']
  rw [hn]
  linarith only [hh]

end
end Cycle12
