import Cycle12.ActualMatchingTeams12
import Cycle12.ActualLowGroupAssembly12

namespace Cycle12
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem verticesWithin_card_le (W A : Finset V) : (verticesWithin W A).card≤A.card := by
  have hi : (verticesWithin W A).image Subtype.val⊆A := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
    exact (mem_verticesWithin W A j).mp hj
  have hc := card_image_of_injective (verticesWithin W A) Subtype.val_injective
  rw [←hc]
  exact card_le_card hi

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

def coreLowTeams (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :
    RequestTeams12 (F.CoreLowPairs P r).Index V (routingTeamSize (logScale (originalLog V) L.stopIndex i)) where
  Team := F.LowGroup P hi r
  finite := inferInstance
  team := F.lowGroup P hi r
  hard := fun j => F.lowGroupPorts P hi r (F.lowGroup P hi r j)
  capacity := by intro t; simpa only [Fintype.card_subtype,teamLoad] using F.lowGroup_capacity P hi r t
  hard_capacity := fun j => F.lowGroupPorts_capacity P hi r _

def boxPairTeams (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :
    RequestTeams12 (F.boxPairs P z).Index V (routingTeamSize (logScale (originalLog V) L.stopIndex i)) :=
  (RequestTeams12.sigma (fun r => F.coreLowTeams P hi ⟨z,r⟩)).extend
    (F.lowPairEmbedding P z)
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1

theorem boxPairTeams_low_hard (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (r : Fin (L.foldCores i z).length) (j : (F.CoreLowPairs P ⟨z,r⟩).Index) :
    (F.boxPairTeams P hi z).hard (F.lowPairEmbedding P z ⟨r,j⟩)=
      F.lowGroupPorts P hi ⟨z,r⟩ (F.lowGroup P hi ⟨z,r⟩ j) :=
  RequestTeams12.extend_hard _ _ _ _

theorem boxPairTeams_low_team (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i)
    (r : Fin (L.foldCores i z).length) (j k : (F.CoreLowPairs P ⟨z,r⟩).Index)
    (he : F.lowGroup P hi ⟨z,r⟩ j=F.lowGroup P hi ⟨z,r⟩ k) :
    (F.boxPairTeams P hi z).team (F.lowPairEmbedding P z ⟨r,j⟩)=
      (F.boxPairTeams P hi z).team (F.lowPairEmbedding P z ⟨r,k⟩) := by
  unfold boxPairTeams
  rw [RequestTeams12.extend_team,RequestTeams12.extend_team]
  change Sum.inl (⟨r,F.lowGroup P hi ⟨z,r⟩ j⟩ : Σ r,F.LowGroup P hi ⟨z,r⟩)=_
  rw [he]
  rfl

variable (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

abbrev ActualJointFamily (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :=
  F.jointFamily P Q D z (F.jointPairNext P hi z) (F.jointPairNext_owner P hi z)

/-- All actual requests are assigned teams and hard sets. Quotient
switches have singleton teams: their within-cycle separation comes from
injectivity of the selected core owner, rather than an extra routing claim. -/
def actualJointTeams (hi : i≤L.stopIndex) (z : L.FoldBoxIndex i) :
    RequestTeams12 (F.ActualJointFamily P Q D hi z).Index V
      (routingTeamSize (logScale (originalLog V) L.stopIndex i)) :=
  (F.boxPairTeams P hi z).sum ((F.boxMatchingTeams P hi z).sum (RequestTeams12.singleton
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1))

abbrev ActualCoreRequest (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) :=
  F.JointCoreIndex P Q D r (F.jointPairNext P hi r.1) (F.jointPairNext_owner P hi r.1)

def actualCoreHard (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) : Finset (L.foldCorePiece i r).vertices :=
  verticesWithin _ ((F.actualJointTeams P Q D hi r.1).hard j.val)

def actualCoreWeight (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) (v : (L.foldCorePiece i r).vertices) : ℝ :=
  match j.val with
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr k) =>
    if v.val∈((D ⟨r.1,k.1⟩).outline k.2.1).vertices\blockUnion (F.ambientBatchActive ⟨r.1,k.1⟩)
      then 1 else 0

theorem actualCoreWeight_nonneg (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) (v : (L.foldCorePiece i r).vertices) :
    0≤F.actualCoreWeight P Q D hi r j v := by
  unfold actualCoreWeight
  split
  · exact le_refl 0
  · exact le_refl 0
  · split <;> norm_num

/-- An unconditional simultaneous routing construction for the actual
prepared paths, actual matchings and actual quotient switches at a core.
Every team/hard/weight hypothesis of the routing theorem is discharged. -/
theorem route_actual_joint_core (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (B : AssignedCoreBanks12 (L.foldCorePiece i r) (logScale (originalLog V) L.stopIndex i)) :
    let next := F.jointPairNext P hi r.1
    let hn := F.jointPairNext_owner P hi r.1
    let H := splitBank ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V)) B.coloring true
    ∃ p : ∀ j : F.ActualCoreRequest P Q D hi r,
        H.Walk (F.jointCoreStart P Q D r next hn j) (F.jointCoreFinish P Q D r next hn j),
      (∀ j,(p j).IsPath ∧ (p j).length≤
        globalRoutingLength (Fintype.card (L.foldCorePiece i r).vertices) (logScale (originalLog V) L.stopIndex i) ∧
        Disjoint (routeInterior (p j)) (F.actualCoreHard P Q D hi r j) ∧
        (∑ v∈routeInterior (p j),F.actualCoreWeight P Q D hi r j v)≤
          (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*
            ∑ v,F.actualCoreWeight P Q D hi r j v) ∧
      (∀ j k,j≠k → Disjoint (p j).edges.toFinset (p k).edges.toFinset) ∧
      (∀ j k,j≠k → (F.actualJointTeams P Q D hi r.1).team j.val=
          (F.actualJointTeams P Q D hi r.1).team k.val →
        Disjoint (routeInterior (p j)) (routeInterior (p k))) := by
  apply F.route_joint_core P Q D r _ _ hi B
    (fun j => (F.actualJointTeams P Q D hi r.1).team j.val)
    (F.actualCoreHard P Q D hi r) (F.actualCoreWeight P Q D hi r)
  · exact (F.actualJointTeams P Q D hi r.1).restrict_load (Function.Embedding.subtype _)
  · intro j
    exact (verticesWithin_card_le _ _).trans ((F.actualJointTeams P Q D hi r.1).hard_capacity j.val)
  · exact F.actualCoreWeight_nonneg P Q D hi r

end ActualFoldStage12
end
end Cycle12.Even12
