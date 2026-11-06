import Cycle12.ActualRoutedPaths12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V] [DecidableEq V]

theorem EvenScaleLayers12.fold_core_vertices_disjoint {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :
    Pairwise (fun r t : Fin (L.foldCores i z).length =>
      Disjoint ((L.foldCores i z).get r).vertices ((L.foldCores i z).get t).vertices) :=
  (L.actual_box_data hi (L.foldParent_mem i z) (L.foldBox_mem i z)).2.1

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def boxRoute (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) :
    G.Walk ((F.ActualJointFamily P Q D hi z).left j) ((F.ActualJointFamily P Q D hi z).right j) :=
  F.actualRoutes P Q D hi ⟨z,(F.ActualJointFamily P Q D hi z).owner j⟩ ⟨j,rfl⟩

theorem boxRoute_isPath (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) : (F.boxRoute P Q D hi z j).IsPath :=
  F.actualRoutes_isPath P Q D hi _ _

theorem boxRoute_support (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) {v : V}
    (hv : v∈(F.boxRoute P Q D hi z j).support) :
    v∈((L.foldCores i z).get ((F.ActualJointFamily P Q D hi z).owner j)).vertices :=
  F.actualRoutes_support P Q D hi _ _ hv

theorem boxRoute_hard (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) :
    Disjoint (routeInterior (F.boxRoute P Q D hi z j)) ((F.actualJointTeams P Q D hi z).hard j) :=
  F.actualRoutes_hard P Q D hi _ _

theorem boxRoute_edges_at_core (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) {r : Fin (L.foldCores i z).length}
    (hr : (F.ActualJointFamily P Q D hi z).owner j=r) :
    (F.boxRoute P Q D hi z j).edgeSet=(F.actualRoutes P Q D hi ⟨z,r⟩ ⟨j,hr⟩).edgeSet := by
  subst r
  rfl

theorem boxRoute_interior_at_core (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) {r : Fin (L.foldCores i z).length}
    (hr : (F.ActualJointFamily P Q D hi z).owner j=r) :
    routeInterior (F.boxRoute P Q D hi z j)=routeInterior (F.actualRoutes P Q D hi ⟨z,r⟩ ⟨j,hr⟩) := by
  subst r
  rfl

theorem boxRoute_edges_disjoint (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :
    Pairwise (fun j k : (F.ActualJointFamily P Q D hi z).Index =>
      Disjoint (F.boxRoute P Q D hi z j).edgeSet (F.boxRoute P Q D hi z k).edgeSet) := by
  intro j k hjk
  by_cases hr : (F.ActualJointFamily P Q D hi z).owner j=(F.ActualJointFamily P Q D hi z).owner k
  · rw [F.boxRoute_edges_at_core P Q D hi z j hr,F.boxRoute_edges_at_core P Q D hi z k rfl]
    exact F.actualRoutes_disjoint P Q D hi _ (fun he => hjk (congrArg Subtype.val he))
  · exact F.actualRoutes_cross_disjoint P Q D hi
      (fun he => hr (eq_of_heq (Sigma.mk.inj he).2)) _ _

theorem boxRoute_team_interiors (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    {j k : (F.ActualJointFamily P Q D hi z).Index} (hjk : j≠k)
    (ht : (F.actualJointTeams P Q D hi z).team j=(F.actualJointTeams P Q D hi z).team k) :
    Disjoint (routeInterior (F.boxRoute P Q D hi z j)) (routeInterior (F.boxRoute P Q D hi z k)) := by
  by_cases hr : (F.ActualJointFamily P Q D hi z).owner j=(F.ActualJointFamily P Q D hi z).owner k
  · rw [F.boxRoute_interior_at_core P Q D hi z j hr,F.boxRoute_interior_at_core P Q D hi z k rfl]
    exact F.actualRoutes_team P Q D hi _ (fun he => hjk (congrArg Subtype.val he)) ht
  · apply (L.fold_core_vertices_disjoint hi z hr).mono
    · intro v hv
      exact F.boxRoute_support P Q D hi z j ((mem_routeInterior_iff _ _).mp hv).1
    · intro v hv
      exact F.boxRoute_support P Q D hi z k ((mem_routeInterior_iff _ _).mp hv).1

theorem boxRoute_descendant_disjoint (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (j : (F.ActualJointFamily P Q D hi z).Index) (t : L.FoldBoxIndex i) :
    Disjoint (F.boxRoute P Q D hi z j).edgeSet (L.foldDescendantGraph i t).edgeSet :=
  F.actualRoutes_descendant_disjoint P Q D hi _ _ t

end ActualFoldStage12
end
end Cycle12.Even12
