import Cycle12.Foundations.DFSPartition
import Cycle12.Foundations.PackingAssembly

namespace Cycle13
open SimpleGraph Finset ReservoirPorts
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k T : ℕ}

theorem DFSBlock.exists_lift_packing (B : DFSBlock G k T) (P : CyclePacking B.localGraph) :
    ∃ Q : CyclePacking B.graph, Q.count=P.count ∧ Q.singles=P.singles := by
  have hh : ∃ Q : CyclePacking (reservoirLift B.vertices B.localGraph),
      Q.count=P.count ∧ Q.singles=P.singles :=
    ⟨P.mapEmbedding (reservoirEmbedding B.vertices),rfl,CyclePacking.singles_mapEmbedding _ _⟩
  rwa [B.lift_localGraph] at hh

/-- Assemble every block on the original vertex set. Neither a boundary
vertex nor an edge is charged again by this assembly. -/
theorem DFSPartition.exists_packing (P : DFSPartition G univ k T)
    (Q : ∀ i, CyclePacking (P.block i).localGraph) :
    ∃ R : CyclePacking G,
      R.count=∑ i, (Q i).count ∧ R.singles=∑ i, (Q i).singles := by
  choose Q' hcount hsing using fun i => (P.block i).exists_lift_packing (Q i)
  have hu : (⋃ i, (P.block i).graph.edgeSet)=G.edgeSet := by
    rw [P.edge_union]
    congr 1
    ext x y
    simp [internalGraph]
  refine ⟨CyclePacking.assemble (fun i => (P.block i).graph)
    (fun i => (P.block i).graph_le) P.edge_disjoint Q',?_,?_⟩
  · rw [CyclePacking.assemble_count]
    exact Finset.sum_congr rfl (fun i _ => hcount i)
  · rw [CyclePacking.assemble_singles _ _ _ hu]
    exact Finset.sum_congr rfl (fun i _ => hsing i)

theorem DFSPartition.sum_local_edges (P : DFSPartition G univ k T) :
    ∑ i, (P.block i).localGraph.edgeSet.ncard=G.edgeSet.ncard := by
  simp_rw [DFSBlock.local_edges]
  rw [P.sum_edges]
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ x y => simp [internalGraph]

end
end Cycle13
