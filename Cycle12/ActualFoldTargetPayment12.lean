import Cycle12.ActualFoldCover12
import Cycle12.ActualCorePayment12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I]

theorem indexed_packing_weight {G : SimpleGraph V} (H : I→SimpleGraph V)
    (hle : ∀ i,H i≤G) (hd : Pairwise (fun i j => Disjoint (H i).edgeSet (H j).edgeSet))
    (hu : (⋃ i,(H i).edgeSet)=G.edgeSet) (Q : ∀ i,CyclePacking (H i)) :
    ∃ P : CyclePacking G,P.weight=∑ i,(Q i).weight := by
  refine ⟨CyclePacking.assemble H hle hd Q,?_⟩
  simp only [CyclePacking.weight,CyclePacking.assemble_count,CyclePacking.assemble_singles H hle hd hu,
    Nat.cast_sum,sum_add_distrib,mul_sum]

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i)

/-- Full physical assembly on the selected cores and the entire frontier.
Every packing here is on an actual, pairwise edge-disjoint original subgraph. -/
theorem actual_fold_target_payment (hi : i≤L.stopIndex) (ih : PotentialBelow (Fintype.card V)) :
    ∃ T : CyclePacking (L.foldTargetGraph i),
      let w := logScale (originalLog V) L.stopIndex i
      T.weight≤(1+C*eta+sigma+1/2048)*L.coreMass i+
        (batchFee w+groupFee w)*F.activeMass+
        C*globalPhi (b*w)*(F.batchMass-kappa*F.activeMass)+lossV w*Fintype.card V := by
  obtain ⟨P,Q,hq,hqsum⟩ := F.ambient_quotient_family hi ih
  let D := F.actualOutlineData P Q
  obtain ⟨core,low,hl,hcore⟩ := F.actual_core_and_low_payment P Q D hi (K:=C) (by norm_num [C]) ih.unweighted
  obtain ⟨matching,hm,hmatch⟩ := F.actual_matching_family_payment P Q D hi
  obtain ⟨quotient,hquot⟩ := F.actual_quotient_family_weight P Q D hi
  have hlow (r : L.FoldCoreIndex i) : (low r).used=(F.actualLowGraph P Q D hi r).edgeSet := by
    rw [F.actualLowGraph_edges P Q D hi r]
    exact hl r
  have hmatching (t : F.MatchingClassIndex) :
      (matching t).used=(F.actualMatchingGraph P Q D hi t).edgeSet := by
    rw [F.actualMatchingGraph_edges P Q D hi t]
    exact hm t
  let packs : ∀ t : F.FoldPieceIndex,CyclePacking (F.foldPieceGraph P Q D hi t) := fun t =>
    match t with
    | .inl r => core r
    | .inr (.inl r) => restrictPacking (low r) (F.actualLowGraph P Q D hi r) (hlow r).le
    | .inr (.inr (.inl t)) => restrictPacking (matching t) (F.actualMatchingGraph P Q D hi t) (hmatching t).le
    | .inr (.inr (.inr t)) => quotient t
  obtain ⟨T,hT⟩ := indexed_packing_weight (F.foldPieceGraph P Q D hi)
    (F.foldPiece_le_target P Q D hi) (F.foldPiece_disjoint P Q D hi)
    (by rw [F.foldPiece_cover P Q D hi,L.foldTarget_edges i]) packs
  refine ⟨T,?_⟩
  dsimp only
  rw [hT]
  have hsum : (∑ t : F.FoldPieceIndex,(packs t).weight)=
      (∑ r : L.FoldCoreIndex i,((core r).weight+((low r).count:ℝ)))+
        (∑ t : F.MatchingClassIndex,((matching t).count:ℝ))+(∑ t : F.BatchIndex,(quotient t).weight) := by
    have hlw (r : L.FoldCoreIndex i) :
        (restrictPacking (low r) (F.actualLowGraph P Q D hi r) (hlow r).le).weight=((low r).count:ℝ) :=
      restrictPacking_full_weight (low r) _ (hlow r)
    have hmw (t : F.MatchingClassIndex) :
        (restrictPacking (matching t) (F.actualMatchingGraph P Q D hi t) (hmatching t).le).weight=
          ((matching t).count:ℝ) := restrictPacking_full_weight (matching t) _ (hmatching t)
    simp only [Fintype.sum_sum_type,packs,foldPieceGraph,Sum.elim_inl,Sum.elim_inr,
      hlw,hmw,sum_add_distrib]
    ring
  rw [hsum]
  have hg := F.actual_group_size_budget hi P
  change (∑ r : L.FoldCoreIndex i,((core r).weight+((low r).count:ℝ)))≤
    (1+sigma+C*eta+1/2048)*L.coreMass i+
      F.preparedPairCount P/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ) at hcore
  nlinarith only [hcore,hmatch,hquot,hqsum,hg]

end ActualFoldStage12
end
end Cycle12.Even12
