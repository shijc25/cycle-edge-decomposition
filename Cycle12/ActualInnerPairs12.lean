import Cycle12.ActualInternalOwnership12
import Cycle12.ActualHighCenterBudget12

namespace Cycle12.OwnedTwoEdgeFamily12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : I→Finset V}

theorem restrict_graph_le (P : OwnedTwoEdgeFamily12 G A) (keep : P.Index→Prop) :
    (P.restrict keep).graph≤P.graph := by
  apply edgeSet_subset_edgeSet.mp
  rw [graph_edges,graph_edges]
  exact P.restrict_used_subset keep

end
end Cycle12.OwnedTwoEdgeFamily12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

def coreInnerPairs (r : L.FoldCoreIndex i) :=
  (F.corePairs P r).restrict (fun j => (F.corePairs P r).center j∈(L.foldCorePiece i r).vertices)

theorem core_inner_external_partition (r : L.FoldCoreIndex i) :
    (F.coreInnerPairs P r).used∪(F.coreExternalPairs P r).used=(F.corePairs P r).used ∧
      Disjoint (F.coreInnerPairs P r).used (F.coreExternalPairs P r).used := by
  have hh := (F.corePairs P r).restrict_partition
    (fun j => (F.corePairs P r).center j∉(L.foldCorePiece i r).vertices)
  have he : (F.coreExternalPairs P r).used∪(F.coreInnerPairs P r).used=(F.corePairs P r).used := by
    simpa only [coreExternalPairs,coreInnerPairs,not_not] using hh.1
  have hd : Disjoint (F.coreExternalPairs P r).used (F.coreInnerPairs P r).used := by
    simpa only [coreExternalPairs,coreInnerPairs,not_not] using hh.2
  exact ⟨by rw [Set.union_comm]; exact he,hd.symm⟩

theorem coreInner_supported (r : L.FoldCoreIndex i) :
    SupportedOn (F.coreInnerPairs P r).graph (L.foldCorePiece i r).vertices := by
  intro x y hxy
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (((F.coreInnerPairs P r).graph_adj x y).mp hxy)
  have hz : (F.coreInnerPairs P r).center j∈(L.foldCorePiece i r).vertices := j.property
  have ha := (F.corePairs_endpoints P r j.val).1
  have hb := (F.corePairs_endpoints P r j.val).2
  rcases hj with he|he <;> rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact ⟨hx.symm ▸ hz,hy.symm ▸ ha⟩
  · exact ⟨hx.symm ▸ ha,hy.symm ▸ hz⟩
  · exact ⟨hx.symm ▸ hz,hy.symm ▸ hb⟩
  · exact ⟨hx.symm ▸ hb,hy.symm ▸ hz⟩

theorem corePairs_cover (z : L.FoldBoxIndex i) :
    (⋃ r : Fin (L.foldCores i z).length,(F.corePairs P ⟨z,r⟩).used)=(F.boxPairs P z).used := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun _ => (F.boxPairs P z).restrict_used_subset _)
  · intro e he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨(F.boxPairs P z).owner j,Set.mem_iUnion.mpr ⟨⟨j,rfl⟩,hj⟩⟩

theorem corePairs_disjoint : Pairwise (fun r t : L.FoldCoreIndex i =>
    Disjoint (F.corePairs P r).used (F.corePairs P t).used) := by
  intro r t hrt
  by_cases h : r.1=t.1
  · rcases r with ⟨z,r⟩
    rcases t with ⟨y,t⟩
    dsimp only at h
    subst y
    apply Set.disjoint_left.mpr
    intro e he hf
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
    have hne : j.val≠k.val := by
      intro he
      have hr : r=t := j.property.symm.trans ((congrArg (F.boxPairs P z).owner he).trans k.property)
      exact hrt (by cases hr; rfl)
    exact Set.disjoint_left.mp ((F.boxPairs P z).disjoint hne) hj hk
  · exact (L.fold_descendants_disjoint i h).mono
      (F.corePairs P r).used_subset (F.corePairs P t).used_subset

/-- The edges given directly to a completion are real internal descendant
edges and whole pairs whose centers already belong to the core. -/
def coreRawGraph (r : L.FoldCoreIndex i) : SimpleGraph V :=
  F.coreInternalGraph P r ⊔ (F.coreInnerPairs P r).graph

theorem coreRaw_supported (r : L.FoldCoreIndex i) :
    SupportedOn (F.coreRawGraph P r) (L.foldCorePiece i r).vertices := by
  intro x y hxy
  rcases hxy with h|h
  · exact F.coreInternal_supported P r h
  · exact F.coreInner_supported P r h

theorem coreRaw_le_descendant (r : L.FoldCoreIndex i) :
    F.coreRawGraph P r≤L.foldDescendantGraph i r.1 := by
  apply sup_le
  · apply edgeSet_subset_edgeSet.mp
    rw [F.coreInternalGraph_edges P r]
    exact Set.inter_subset_left.trans (F.boxInternal_subset P r.1)
  · exact (F.coreInnerPairs P r).graph_le

end ActualFoldStage12
end
end Cycle12.Even12
