import Cycle12.ActualInnerPairs12
import Cycle12.SupportedHighCenterCompletion12
import Cycle12.ActualLowClosure12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

/-- Only low pairs, matching requests and quotient switches consume routes.
Auxiliary routes for internal pairs and high pairs are deliberately retained. -/
def actualUsedRequest (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) : Prop :=
  match j.val with
  | .inl k => k∈Set.range (F.lowPairEmbedding P r.1)
  | .inr _ => True

def coreUsedRoutes (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  {e | ∃ j : F.ActualCoreRequest P Q D hi r,
    F.actualUsedRequest P Q D hi r j ∧ e∈(F.actualRoutes P Q D hi r j).edgeSet}

def actualRoutingEdges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  Sym2.map (Subtype.val : (L.foldCorePiece i r).vertices→V) '' (F.actualRoutingBank hi r).edgeSet

theorem actualRoutes_edges_bank (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) :
    (F.actualRoutes P Q D hi r j).edgeSet⊆F.actualRoutingEdges hi r := by
  rw [actualRoutes,Walk.edgeSet_map]
  exact Set.image_mono (F.actualBankPaths P Q D hi r j).edges_subset_edgeSet

theorem coreUsedRoutes_bank (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    F.coreUsedRoutes P Q D hi r⊆F.actualRoutingEdges hi r := by
  rintro e ⟨j,_,he⟩
  exact F.actualRoutes_edges_bank P Q D hi r j he

theorem coreUsedRoutes_core (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    F.coreUsedRoutes P Q D hi r⊆(L.foldCorePiece i r).graph.edgeSet := by
  rintro e ⟨j,_,he⟩
  exact F.actualRoutes_edges_core P Q D hi r j he

theorem lowRoute_used (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    (F.actualLowRoute P Q D hi r j).edgeSet⊆F.coreUsedRoutes P Q D hi r := by
  rw [F.actualLowRoute_edges P Q D hi r j]
  intro e he
  exact ⟨F.lowRequest P Q D hi r j,⟨⟨r.2,j⟩,rfl⟩,he⟩

/-- The reserved false bank is the bank fixed before simultaneous routing. -/
def actualCompletionGraph (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : SimpleGraph V :=
  reservoirLift (L.foldCorePiece i r).vertices
    (splitBank ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V))
      (F.actualBank hi r).coloring false)

def coreUnusedGraph (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : SimpleGraph V :=
  (L.foldCorePiece i r).graph.deleteEdges (F.coreUsedRoutes P Q D hi r)

theorem completionBank_survives (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    F.actualCompletionGraph hi r≤F.coreUnusedGraph P Q D hi r := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ :=
    (SimpleGraph.map_adj (reservoirEmbedding (L.foldCorePiece i r).vertices) _ x y).mp hxy
  apply deleteEdges_adj.mpr
  refine ⟨huv.1,?_⟩
  intro he
  obtain ⟨e,he,hm⟩ := F.coreUsedRoutes_bank P Q D hi r he
  have hid : e=s(u,v) := (Sym2.map.injective Subtype.val_injective) hm
  subst e
  have ht : (F.actualBank hi r).coloring s(u,v)=true := he.2
  have hf : (F.actualBank hi r).coloring s(u,v)=false := huv.2
  exact Bool.noConfusion (hf.symm.trans ht)

theorem coreUnused_expansion (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    OAI.ErdosGallai.Scale.CutExpansionOn (F.coreUnusedGraph P Q D hi r)
      (L.foldCorePiece i r).vertices
      (completion_bank*(2:ℝ)^(s*logScale (originalLog V) L.stopIndex i)) := by
  apply cutExpansionOn_graph_mono (G:=F.actualCompletionGraph hi r)
  · apply cutExpansionOn_of_induce
    simpa only [actualCompletionGraph,induce_reservoirLift] using (F.actualBank hi r).completion
  · exact F.completionBank_survives P Q D hi r

/-- The concrete selected-core completion graph contains no invented edges. -/
def coreCompletionGraph (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : SimpleGraph V :=
  (F.coreUnusedGraph P Q D hi r ⊔ F.coreRawGraph P r) ⊔ (F.coreHighPairs P r).graph

def coreCompletionVertices (r : L.FoldCoreIndex i) : Finset V :=
  (L.foldCorePiece i r).vertices∪F.coreHighCenters P r

theorem coreCompletion_supported (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    SupportedOn (F.coreCompletionGraph P Q D hi r) (F.coreCompletionVertices P r) := by
  intro x y hxy
  rcases hxy with (h|h)|h
  · have hs := (L.foldCorePiece i r).supported (deleteEdges_adj.mp h).1
    exact ⟨mem_union_left _ hs.1,mem_union_left _ hs.2⟩
  · have hs := F.coreRaw_supported P r h
    exact ⟨mem_union_left _ hs.1,mem_union_left _ hs.2⟩
  · exact F.coreHigh_supported P r h

theorem coreCompletion_le_original (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    F.coreCompletionGraph P Q D hi r≤G := by
  have hdesc : L.foldDescendantGraph i r.1≤G :=
    (L.fold_descendant_le_box i r.1).trans
      ((L.fold_box_le_parent i r.1).trans (L.fold_parent_le_original i r.1))
  apply sup_le
  · apply sup_le
    · intro x y h
      exact L.fold_core_le_original i r (deleteEdges_adj.mp h).1
    · exact (F.coreRaw_le_descendant P r).trans hdesc
  · exact (F.coreHighPairs P r).graph_le.trans hdesc

theorem coreCompletion_outside_adj (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    {x y : V} (hx : x∉(L.foldCorePiece i r).vertices) :
    (F.coreCompletionGraph P Q D hi r).Adj x y ↔ (F.coreHighPairs P r).graph.Adj x y := by
  constructor
  · intro h
    rcases h with (h|h)|h
    · exact False.elim (hx ((L.foldCorePiece i r).supported (deleteEdges_adj.mp h).1).1)
    · exact False.elim (hx (F.coreRaw_supported P r h).1)
    · exact h
  · exact Or.inr

theorem coreCompletion_outside_degree (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    (F.coreCompletionGraph P Q D hi r).degree v=(F.coreHighPairs P r).graph.degree v := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  congr 1
  ext x
  simp only [mem_neighborFinset,F.coreCompletion_outside_adj P Q D hi r hv]

theorem coreCompletion_expansion (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    OAI.ErdosGallai.Scale.CutExpansionOn (F.coreCompletionGraph P Q D hi r)
      (L.foldCorePiece i r).vertices
      (completion_bank*(2:ℝ)^(s*logScale (originalLog V) L.stopIndex i)) :=
  cutExpansionOn_graph_mono (F.coreUnused_expansion P Q D hi r)
    (le_sup_left.trans le_sup_left)

end ActualFoldStage12
end
end Cycle12.Even12
