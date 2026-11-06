import Cycle12.ActualBatchPotential12
import Cycle12.PreparedBlockClasses12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def localBatchGraph (F : ActualFoldStage12 L i) (t : F.BatchIndex) :
    SimpleGraph (F.batchVertices t) := (F.batchGraph t).induce (F.batchVertices t:Set V)

def BatchPreparation (F : ActualFoldStage12 L i) (t : F.BatchIndex) :=
  PreparedBlockBatch12 (F.localBatchGraph t) (F.batchActive t)
    (routingTeamSize (logScale (originalLog V) L.stopIndex i))

theorem batchPreparation_exists (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (t : F.BatchIndex) : Nonempty (F.BatchPreparation t) :=
  prepared_block_batch_exists (F.localBatchGraph t) (F.batchActive t) (F.batchActive_disjoint t)
    (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1

/-- Choose an actual preparation and an actual quotient packing in every
batch. Every local matching/pairing witness remains available afterwards. -/
theorem prepared_quotient_family (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (ih : PotentialBelow (Fintype.card V)) :
    ∃ P : ∀ t : F.BatchIndex,F.BatchPreparation t,
      ∃ pack : ∀ t,CyclePacking ((P t).retained.map (contractVertex (F.batchActive t))),
        (∀ t,(P t).retained ≤ F.localBatchGraph t ∧
          (∀ {x y},(P t).retained.Adj x y → contractVertex (F.batchActive t) x ≠ contractVertex (F.batchActive t) y) ∧
          Set.InjOn (Sym2.map (contractVertex (F.batchActive t))) (P t).retained.edgeSet) ∧
        (∀ t,(pack t).weight ≤ C*globalPhi (b*logScale (originalLog V) L.stopIndex i)*
          (((F.batchVertices t).card:ℝ)-kappa*∑ j,(((F.active t.1).vertices t.2 j).card:ℝ))) ∧
        (∑ t,(pack t).weight) ≤ C*globalPhi (b*logScale (originalLog V) L.stopIndex i)*
          (F.batchMass-kappa*F.activeMass) := by
  let P : ∀ t : F.BatchIndex,F.BatchPreparation t :=
    fun t => Classical.choice (F.batchPreparation_exists hi t)
  choose pack hpack using fun t : F.BatchIndex => F.contracted_batch_packing hi ih t (P t).retained
  refine ⟨P,pack,fun t => (P t).quotient_unique (F.batchActive_disjoint t),hpack,?_⟩
  have hh := sum_le_sum (fun t (_ : t∈(univ:Finset F.BatchIndex)) => hpack t)
  simp only [←mul_sum,sum_sub_distrib] at hh
  have hb : (∑ t : F.BatchIndex,((F.batchVertices t).card:ℝ))=F.batchMass := by
    rw [Fintype.sum_sigma]
    rfl
  have ha : (∑ t : F.BatchIndex,∑ j,(((F.active t.1).vertices t.2 j).card:ℝ))=F.activeMass := by
    rw [Fintype.sum_sigma]
    rfl
  rwa [hb,ha] at hh

end ActualFoldStage12
end
end Cycle12.Even12
