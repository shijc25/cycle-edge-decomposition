import Cycle12.ActualJointRoutingData12
import Cycle12.RouteEmbedding12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def actualBank (_F : ActualFoldStage12 L i) (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    AssignedCoreBanks12 (L.foldCorePiece i r) (logScale (originalLog V) L.stopIndex i) :=
  Classical.choice (L.fold_core_banks hi r)

def actualRoutingBank (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    SimpleGraph (L.foldCorePiece i r).vertices :=
  splitBank ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V))
    (F.actualBank hi r).coloring true

abbrev actualStart (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :=
  F.jointCoreStart P Q D r (F.jointPairNext P hi r.1) (F.jointPairNext_owner P hi r.1)

abbrev actualFinish (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :=
  F.jointCoreFinish P Q D r (F.jointPairNext P hi r.1) (F.jointPairNext_owner P hi r.1)

def actualBankPaths (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    ∀ j : F.ActualCoreRequest P Q D hi r,
      (F.actualRoutingBank hi r).Walk (F.actualStart P Q D hi r j) (F.actualFinish P Q D hi r j) :=
  Classical.choose (F.route_actual_joint_core P Q D hi r (F.actualBank hi r))

theorem actualBankPaths_spec (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    (∀ j,(F.actualBankPaths P Q D hi r j).IsPath ∧
      (F.actualBankPaths P Q D hi r j).length≤
        globalRoutingLength (Fintype.card (L.foldCorePiece i r).vertices) (logScale (originalLog V) L.stopIndex i) ∧
      Disjoint (routeInterior (F.actualBankPaths P Q D hi r j)) (F.actualCoreHard P Q D hi r j) ∧
      (∑ v∈routeInterior (F.actualBankPaths P Q D hi r j),F.actualCoreWeight P Q D hi r j v)≤
        (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
          ∑ v,F.actualCoreWeight P Q D hi r j v) ∧
    (∀ j k,j≠k → Disjoint (F.actualBankPaths P Q D hi r j).edges.toFinset
      (F.actualBankPaths P Q D hi r k).edges.toFinset) ∧
    (∀ j k,j≠k → (F.actualJointTeams P Q D hi r.1).team j.val=
        (F.actualJointTeams P Q D hi r.1).team k.val →
      Disjoint (routeInterior (F.actualBankPaths P Q D hi r j))
        (routeInterior (F.actualBankPaths P Q D hi r k))) :=
  Classical.choose_spec (F.route_actual_joint_core P Q D hi r (F.actualBank hi r))

abbrev actualBankHom (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : F.actualRoutingBank hi r →g G :=
  ⟨Subtype.val,fun h => L.fold_core_le_original i r h.1⟩

def actualRoutes (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) (j : F.ActualCoreRequest P Q D hi r) :
    G.Walk (F.actualStart P Q D hi r j).val (F.actualFinish P Q D hi r j).val :=
  (F.actualBankPaths P Q D hi r j).map (F.actualBankHom hi r)

theorem actualRoutes_isPath (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) : (F.actualRoutes P Q D hi r j).IsPath :=
  ((F.actualBankPaths_spec P Q D hi r).1 j).1.map Subtype.val_injective

theorem actualRoutes_support (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) {v : V}
    (hv : v∈(F.actualRoutes P Q D hi r j).support) : v∈(L.foldCorePiece i r).vertices := by
  rw [actualRoutes,Walk.support_map] at hv
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
  exact x.property

theorem actualRoutes_edges_core (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) :
    (F.actualRoutes P Q D hi r j).edgeSet⊆(L.foldCorePiece i r).graph.edgeSet := by
  rw [actualRoutes,Walk.edgeSet_map]
  rintro _ ⟨e,he,rfl⟩
  have hh := (F.actualBankPaths P Q D hi r j).edges_subset_edgeSet he
  induction e using Sym2.ind with
  | _ x y => exact hh.1

theorem actualRoutes_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    Pairwise (fun j k : F.ActualCoreRequest P Q D hi r =>
      Disjoint (F.actualRoutes P Q D hi r j).edgeSet (F.actualRoutes P Q D hi r k).edgeSet) := by
  intro j k hjk
  simp only [actualRoutes,Walk.edgeSet_map]
  apply disjoint_set_image _ (Sym2.map.injective Subtype.val_injective)
  apply Set.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp ((F.actualBankPaths_spec P Q D hi r).2.1 j k hjk)
    (List.mem_toFinset.mpr he) (List.mem_toFinset.mpr hf)

theorem actualRoutes_cross_disjoint (hi : i≤L.stopIndex) {r t : L.FoldCoreIndex i} (hrt : r≠t)
    (j : F.ActualCoreRequest P Q D hi r) (k : F.ActualCoreRequest P Q D hi t) :
    Disjoint (F.actualRoutes P Q D hi r j).edgeSet (F.actualRoutes P Q D hi t k).edgeSet :=
  (L.fold_core_edge_disjoint hi hrt).mono (F.actualRoutes_edges_core P Q D hi r j)
    (F.actualRoutes_edges_core P Q D hi t k)

theorem actualRoutes_hard (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) :
    Disjoint (routeInterior (F.actualRoutes P Q D hi r j))
      ((F.actualJointTeams P Q D hi r.1).hard j.val) := by
  rw [actualRoutes,routeInterior_map_injective (F.actualBankHom hi r) Subtype.val_injective]
  apply Finset.disjoint_left.mpr
  intro v hv hh
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
  apply Finset.disjoint_left.mp (((F.actualBankPaths_spec P Q D hi r).1 j).2.2.1) hx
  exact (mem_verticesWithin _ _ x).mpr hh

theorem actualRoutes_team (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    {j k : F.ActualCoreRequest P Q D hi r} (hjk : j≠k)
    (ht : (F.actualJointTeams P Q D hi r.1).team j.val=
      (F.actualJointTeams P Q D hi r.1).team k.val) :
    Disjoint (routeInterior (F.actualRoutes P Q D hi r j))
      (routeInterior (F.actualRoutes P Q D hi r k)) := by
  simp only [actualRoutes,routeInterior_map_injective (F.actualBankHom hi r) Subtype.val_injective]
  exact disjoint_finset_image _ Subtype.val_injective
    ((F.actualBankPaths_spec P Q D hi r).2.2 j k hjk ht)

/-- All selected routing edges avoid all descendant originals, including
originals owned by a different parent box. -/
theorem actualRoutes_descendant_disjoint (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) (z : L.FoldBoxIndex i) :
    Disjoint (F.actualRoutes P Q D hi r j).edgeSet (L.foldDescendantGraph i z).edgeSet :=
  (L.fold_core_descendants_disjoint hi r.1 z r.2).mono
    (F.actualRoutes_edges_core P Q D hi r j) subset_rfl

end ActualFoldStage12
end
end Cycle12.Even12
