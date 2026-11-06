import Cycle12.ActualRoutedPaths12
import Cycle12.LowPathGroupClosure12

namespace Cycle12
open Cycle13 SimpleGraph Finset
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}
theorem routeInterior_copy {a b a' b' : V} (p : G.Walk a b) (ha : a=a') (hb : b=b') :
    routeInterior (p.copy ha hb)=routeInterior p := by subst a'; subst b'; rfl
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def lowRequest (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) : F.ActualCoreRequest P Q D hi r :=
  ⟨Sum.inl (F.lowPairEmbedding P r.1 ⟨r.2,j⟩),F.lowPairEmbedding_owner P r.1 ⟨r.2,j⟩⟩

theorem lowRequest_injective (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    Function.Injective (F.lowRequest P Q D hi r) := by
  intro j k he
  have hh := Sum.inl.inj (congrArg Subtype.val he)
  have hs := (F.lowPairEmbedding P r.1).injective hh
  exact eq_of_heq (Sigma.mk.inj hs).2

theorem lowRequest_start (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    (F.actualStart P Q D hi r (F.lowRequest P Q D hi r j)).val=(F.CoreLowPairs P r).right j := rfl

theorem lowRequest_finish (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    (F.actualFinish P Q D hi r (F.lowRequest P Q D hi r j)).val=
      (F.CoreLowPairs P r).left (groupedCycleNext (F.lowGroup P hi r) j) := by
  change (F.boxPairs P r.1).left
    (F.jointPairNext P hi r.1 (F.lowPairEmbedding P r.1 ⟨r.2,j⟩))=_
  rw [F.jointPairNext_on_low P hi r.1 r.2 j]
  rfl

def actualLowRoute (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    G.Walk ((F.CoreLowPairs P r).right j)
      ((F.CoreLowPairs P r).left (groupedCycleNext (F.lowGroup P hi r) j)) :=
  (F.actualRoutes P Q D hi r (F.lowRequest P Q D hi r j)).copy
    (F.lowRequest_start P Q D hi r j) (F.lowRequest_finish P Q D hi r j)

theorem actualLowRoute_isPath (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) : (F.actualLowRoute P Q D hi r j).IsPath := by
  rw [actualLowRoute,Walk.isPath_copy]
  exact F.actualRoutes_isPath P Q D hi r _

theorem actualLowRoute_support (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) {v : V}
    (hv : v∈(F.actualLowRoute P Q D hi r j).support) : v∈(L.foldCorePiece i r).vertices := by
  rw [actualLowRoute,Walk.support_copy] at hv
  exact F.actualRoutes_support P Q D hi r _ hv

theorem actualLowRoute_edges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    (F.actualLowRoute P Q D hi r j).edgeSet=
      (F.actualRoutes P Q D hi r (F.lowRequest P Q D hi r j)).edgeSet :=
  Walk.edgeSet_copy _ _ _

theorem actualLowRoute_hard (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : (F.CoreLowPairs P r).Index) :
    Disjoint (routeInterior (F.actualLowRoute P Q D hi r j))
      (F.lowGroupPorts P hi r (F.lowGroup P hi r j)) := by
  have hh := F.actualRoutes_hard P Q D hi r (F.lowRequest P Q D hi r j)
  change Disjoint _ ((F.boxPairTeams P hi r.1).hard (F.lowPairEmbedding P r.1 ⟨r.2,j⟩)) at hh
  rw [F.boxPairTeams_low_hard P hi r.1 r.2 j] at hh
  simpa only [actualLowRoute,routeInterior_copy] using hh

theorem actualLowRoute_team (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    {j k : (F.CoreLowPairs P r).Index} (hjk : j≠k)
    (ht : F.lowGroup P hi r j=F.lowGroup P hi r k) :
    Disjoint (routeInterior (F.actualLowRoute P Q D hi r j))
      (routeInterior (F.actualLowRoute P Q D hi r k)) := by
  have hh := F.actualRoutes_team P Q D hi r ((F.lowRequest_injective P Q D hi r).ne hjk)
    (j:=F.lowRequest P Q D hi r j) (k:=F.lowRequest P Q D hi r k) (by
      change Sum.inl ((F.boxPairTeams P hi r.1).team (F.lowPairEmbedding P r.1 ⟨r.2,j⟩))=
        Sum.inl ((F.boxPairTeams P hi r.1).team (F.lowPairEmbedding P r.1 ⟨r.2,k⟩))
      exact congrArg Sum.inl (F.boxPairTeams_low_team P hi r.1 r.2 j k ht))
  simpa only [actualLowRoute,routeInterior_copy] using hh

/-- The low-path cycles now use the paths from the same simultaneous
call as matching and quotient requests. Their edge set is exact. -/
theorem actual_low_closure (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    ∃ T : CyclePacking G,T.used=(F.CoreLowPairs P r).used∪
      (⋃ j,(F.actualLowRoute P Q D hi r j).edgeSet) ∧
      (T.count:ℝ)≤(Fintype.card (F.CoreLowPairs P r).Index:ℝ)/
        routingTeamSize (logScale (originalLog V) L.stopIndex i)+
        2*routingAllowance (logScale (originalLog V) L.stopIndex i)+F.coreCenterThreshold r/2 := by
  let E := F.CoreLowPairs P r
  have hFG : L.foldDescendantGraph i r.1≤G :=
    (L.fold_descendant_le_box i r.1).trans
      ((L.fold_box_le_parent i r.1).trans (L.fold_parent_le_original i r.1))
  have hPP : Pairwise (fun j k : E.Index =>
      Disjoint (twoEdgeWalk (hFG (E.adj_left j)) (hFG (E.adj_right j))).edgeSet
        (twoEdgeWalk (hFG (E.adj_left k)) (hFG (E.adj_right k))).edgeSet) := by
    simpa only [twoEdgeWalk_edges] using E.disjoint
  obtain ⟨T,hT,hcount⟩ := low_path_group_closure (L.foldCorePiece i r).vertices E.left E.right E.center
    (fun j => hFG (E.adj_left j)) (fun j => hFG (E.adj_right j)) E.distinct
    (fun j => (F.coreExternal_endpoints P r j.val).1)
    (fun j => (F.coreExternal_endpoints P r j.val).2)
    (fun j => F.coreExternal_outside P r j.val) hPP
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1
    (F.lowColor P hi r) (F.actualLowRoute P Q D hi r)
    (F.actualLowRoute_isPath P Q D hi r)
    (fun j _ hv => F.actualLowRoute_support P Q D hi r j hv)
    (F.actualLowRoute_hard P Q D hi r) (by
      intro j k hjk
      rw [F.actualLowRoute_edges P Q D hi r j,F.actualLowRoute_edges P Q D hi r k]
      exact F.actualRoutes_disjoint P Q D hi r ((F.lowRequest_injective P Q D hi r).ne hjk))
    (by
      intro j k
      rw [F.actualLowRoute_edges P Q D hi r k]
      apply (F.actualRoutes_descendant_disjoint P Q D hi r _ r.1).symm.mono _ subset_rfl
      simpa only [twoEdgeWalk_edges,OwnedTwoEdgeFamily12.edges] using E.edges_subset j)
    (fun j k hjk ht => F.actualLowRoute_team P Q D hi r hjk ht)
  refine ⟨T,?_,?_⟩
  · simpa only [E,OwnedTwoEdgeFamily12.used,OwnedTwoEdgeFamily12.edges,twoEdgeWalk_edges] using hT
  · have hh := OwnedTwoEdgeFamily12.low_palette_cost
      (routingAllowance_pos (logScale (originalLog V) L.stopIndex i)).le
      (show 0≤F.coreCenterThreshold r from Nat.cast_nonneg _)
    exact hcount.trans (by linarith only [hh])

end ActualFoldStage12
end
end Cycle12.Even12
