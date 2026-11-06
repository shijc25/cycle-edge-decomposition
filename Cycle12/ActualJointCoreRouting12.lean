import Cycle12.ActualJointRequestFamily12

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
  (r : L.FoldCoreIndex i) (next : Equiv.Perm (F.boxPairs P r.1).Index)
  (hn : ∀ j,(F.boxPairs P r.1).owner (next j)=(F.boxPairs P r.1).owner j)

abbrev JointCoreIndex :=
  {j : (F.jointFamily P Q D r.1 next hn).Index //
    (F.jointFamily P Q D r.1 next hn).owner j=r.2}

def jointCoreStart (j : F.JointCoreIndex P Q D r next hn) : (L.foldCorePiece i r).vertices :=
  ⟨(F.jointFamily P Q D r.1 next hn).left j.val,by
    have h := (F.jointFamily P Q D r.1 next hn).left_mem j.val
    rw [j.property] at h
    exact h⟩

def jointCoreFinish (j : F.JointCoreIndex P Q D r next hn) : (L.foldCorePiece i r).vertices :=
  ⟨(F.jointFamily P Q D r.1 next hn).right j.val,by
    have h := (F.jointFamily P Q D r.1 next hn).right_mem j.val
    rw [j.property] at h
    exact h⟩

def jointCoreCertificate : OriginalEndpointCertificate (L.foldDescendantGraph i r.1)
    (fun j => (F.jointCoreStart P Q D r next hn j).val)
    (fun j => (F.jointCoreFinish P Q D r next hn j).val)
    ((F.boxPairs P r.1).used∪(F.boxMatchingEdges P r.1∪F.boxQuotientEdges P Q D r.1)) :=
  (F.jointFamily P Q D r.1 next hn).certificate.restrict (Function.Embedding.subtype _)

theorem jointCore_good (j : F.JointCoreIndex P Q D r next hn) :
    (F.jointCoreStart P Q D r next hn j).val∈F.activeVertices r.1 ∧
      (F.jointCoreFinish P Q D r next hn j).val∈F.activeVertices r.1 :=
  F.jointFamily_good P Q D r.1 next hn j.val

/-- All actual origins are passed to one call in this selected core.
Only the still-to-be-assembled team, hard-port and soft-weight payload is
supplied here; original-edge injectivity and degree bounds are discharged. -/
theorem route_joint_core {T : Type} [Fintype T]
    (hi : i ≤ L.stopIndex)
    (B : AssignedCoreBanks12 (L.foldCorePiece i r) (logScale (originalLog V) L.stopIndex i))
    (team : F.JointCoreIndex P Q D r next hn → T)
    (hard : F.JointCoreIndex P Q D r next hn → Finset (L.foldCorePiece i r).vertices)
    (weight : F.JointCoreIndex P Q D r next hn → (L.foldCorePiece i r).vertices → ℝ)
    (hteam : ∀ t,teamLoad team t ≤ routingTeamSize (logScale (originalLog V) L.stopIndex i))
    (hhard : ∀ j,(hard j).card ≤ 2*routingTeamSize (logScale (originalLog V) L.stopIndex i))
    (hweight : ∀ j v,0 ≤ weight j v) :
    let H := splitBank ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V)) B.coloring true
    ∃ p : ∀ j,H.Walk (F.jointCoreStart P Q D r next hn j) (F.jointCoreFinish P Q D r next hn j),
      (∀ j,(p j).IsPath ∧ (p j).length ≤
        globalRoutingLength (Fintype.card (L.foldCorePiece i r).vertices) (logScale (originalLog V) L.stopIndex i) ∧
        Disjoint (routeInterior (p j)) (hard j) ∧
        (∑ v∈routeInterior (p j),weight j v) ≤
          (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*∑ v,weight j v) ∧
      (∀ j k,j ≠ k → Disjoint (p j).edges.toFinset (p k).edges.toFinset) ∧
      (∀ j k,j ≠ k → team j=team k → Disjoint (routeInterior (p j)) (routeInterior (p k))) := by
  letI : DecidableEq (F.JointCoreIndex P Q D r next hn) := Classical.decEq _
  apply F.route_actual_core hi r B (F.jointCoreStart P Q D r next hn)
    (F.jointCoreFinish P Q D r next hn) team hard weight _
    (F.jointCoreCertificate P Q D r next hn)
  · rintro ⟨j,t⟩
    cases t with
    | false => exact (F.jointCore_good P Q D r next hn j).1
    | true => exact (F.jointCore_good P Q D r next hn j).2
  · exact hteam
  · exact hhard
  · exact hweight

end ActualFoldStage12
end
end Cycle12.Even12
