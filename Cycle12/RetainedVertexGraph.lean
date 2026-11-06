import Cycle12.GraphJansonSharp
import Cycle12.Foundations.VertexDeletionEdges
import Cycle12.Foundations.SampledCutComparison

namespace Cycle12
open Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Keep the original vertex type and retain exactly the edges within D.
The vertices outside D are isolated; this permits sampling directly on D. -/
def retainedVertexGraph (G : SimpleGraph V) (D : Finset V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ v∈D ∧ w∈D
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

theorem retained_vertex_graph_le (G : SimpleGraph V) (D : Finset V) :
    retainedVertexGraph G D≤G := fun _ _ h => h.1

theorem retained_vertex_graph_support (G : SimpleGraph V) (D : Finset V) :
    (retainedVertexGraph G D).support⊆(D:Set V) := by
  rintro v ⟨w,hw⟩
  exact hw.2.1

theorem retained_vertex_graph_induce (G : SimpleGraph V) (D : Finset V) :
    (retainedVertexGraph G D).induce (D:Set V)=G.induce (D:Set V) := by
  ext v w
  change (G.Adj v.val w.val ∧ v.val∈D ∧ w.val∈D) ↔ G.Adj v.val w.val
  exact ⟨fun h => h.1, fun h => ⟨h,v.property,w.property⟩⟩

theorem retained_vertex_graph_edge_count (G : SimpleGraph V) (D : Finset V) :
    Fintype.card (retainedVertexGraph G D).edgeSet=inducedEdgeCount G D := by
  have hc := (retainedVertexGraph G D).card_edgeFinset_induce_of_support_subset
    (retained_vertex_graph_support G D)
  simp only [← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card] at hc
  have hh := congrArg (fun H : SimpleGraph (D:Set V) => Nat.card H.edgeSet)
    (retained_vertex_graph_induce G D)
  have he := hc.symm.trans hh
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet,inducedEdgeCount] using he

theorem retained_vertex_graph_edge_support (G : SimpleGraph V) (D : Finset V)
    (e : (retainedVertexGraph G D).edgeSet) :
    edgeVertexSet (retainedVertexGraph G D) e⊆D := by
  intro v hv
  have hm : v∈e.val := by simpa only [edgeVertexSet,Sym2.mem_toFinset] using hv
  obtain ⟨w,hw⟩ := Sym2.mem_iff_exists.mp hm
  have ha := e.property
  rw [hw] at ha
  exact ((retainedVertexGraph G D).mem_edgeSet.mp ha).2.1

theorem sampled_finset_edge_count_eq_sampled (G : SimpleGraph V) (D : Finset V) :
    sampledFinsetEdgeCount G D=sampledEdgeCount G (D:Set V) := by
  rw [sampledFinsetEdgeCount,sampledEdgeCount,Set.ncard_eq_toFinset_card']
  apply congrArg Finset.card
  ext e
  simp only [mem_filter,mem_univ,true_and]
  have hh := @Set.mem_toFinset G.edgeSet
    {e : G.edgeSet | (edgeVertexSet G e:Set V)⊆(D:Set V)} (Subtype.fintype _) e
  simpa only [Set.mem_setOf_eq,Finset.coe_subset] using hh.symm

theorem sampled_finset_edge_count_eq_induced (G : SimpleGraph V) (D : Finset V) :
    sampledFinsetEdgeCount G D=inducedEdgeCount G D := by
  rw [sampled_finset_edge_count_eq_sampled,sampledEdgeCount_eq_inducedEdgeCount]

theorem sampled_finset_edge_count_graph_mono {H G : SimpleGraph V} (hHG : H≤G)
    (S : Finset V) : sampledFinsetEdgeCount H S ≤ sampledFinsetEdgeCount G S := by
  simp only [sampled_finset_edge_count_eq_sampled]
  exact sampledEdgeCount_mono hHG _

theorem retained_vertex_graph_deletion_bound (G : SimpleGraph V) (T : Finset V)
    {k : ℕ} (hdeg : ∀ v∈T, G.degree v≤k) :
    (Fintype.card G.edgeSet:ℝ)-(k:ℝ)*T.card ≤
      (Fintype.card (retainedVertexGraph G (univ\T)).edgeSet:ℝ) := by
  rw [retained_vertex_graph_edge_count]
  simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using
    edge_count_delete_vertices_bounded G T hdeg

end
end Cycle12
