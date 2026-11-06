import Cycle12.ActualFoldIndex12
import Cycle12.ActualFoldPrefixMass12
import Cycle12.ActiveDeficitPayment12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
open OAI.ErdosGallai.Indexing (GraphBatches ActiveFamily)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Actual descendant batches and active blocks at every indexed box of
one stage. The exact local descendant mass is retained in each batch. -/
structure ActualFoldStage12 {G : SimpleGraph V} (L : EvenScaleLayers12 G) (i : ℕ) where
  batches : ∀ z : L.FoldBoxIndex i,
    GraphBatches (L.foldDescendantGraph i z) (L.foldBox i z).vertices
      ((2:ℝ)^(b*logScale (originalLog V) L.stopIndex i)) (vertexMass (L.foldDescendants i z))
  active : ∀ z : L.FoldBoxIndex i,
    ActiveFamily (L.foldDescendantGraph i z) (L.foldBox i z).vertices (batches z).vertices
      (fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices)
      ((2:ℝ)^(alpha*logScale (originalLog V) L.stopIndex i))
      ((2:ℝ)^(lam*logScale (originalLog V) L.stopIndex i))
  injective : ∀ z t,Function.Injective ((active z).router t)
  deficit : ∀ z,vertexMass (L.foldCores i z)-
    parentDeficitFee (logScale (originalLog V) L.stopIndex i)*(L.foldBox i z).vertices.card ≤
      ∑ t,∑ j,(((active z).vertices t j).card:ℝ)

theorem EvenScaleLayers12.actual_fold_stage {G : SimpleGraph V} (L : EvenScaleLayers12 G)
    {i : ℕ} (hi : i ≤ L.stopIndex) : Nonempty (ActualFoldStage12 L i) := by
  choose B A hinj hlo hhi using L.fold_box_active_exact hi
  refine ⟨⟨B,A,hinj,?_⟩⟩
  intro z
  have hh := parent_active_deficit_payment (Nat.cast_nonneg (L.foldBox i z).vertices.card)
    (L.fold_box_order hi z) (hlo z)
  have he : (∑ r : Fin (L.foldCores i z).length,
      (((L.foldCores i z).get r).vertices.card:ℝ))=vertexMass (L.foldCores i z) :=
    list_sum_get _ (fun R : AssignedPiece V => (R.vertices.card:ℝ))
  rwa [he] at hh

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

abbrev BatchIndex (F : ActualFoldStage12 L i) := (z : L.FoldBoxIndex i) × (F.batches z).Index

def batchMass (F : ActualFoldStage12 L i) : ℝ :=
  ∑ z,∑ t,(((F.batches z).vertices t).card:ℝ)

def activeMass (F : ActualFoldStage12 L i) : ℝ :=
  ∑ z,∑ t,∑ j,(((F.active z).vertices t j).card:ℝ)

theorem activeMass_nonneg (F : ActualFoldStage12 L i) : 0 ≤ F.activeMass :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => Nat.cast_nonneg _)))

theorem batchMass_le_descendants (F : ActualFoldStage12 L i) :
    F.batchMass ≤ vertexMass (advance L.splitter 0 (i+3) [originalPiece G]) := by
  rw [←L.fold_descendant_mass i]
  exact sum_le_sum (fun z _ => (F.batches z).mass_le)

theorem activeMass_lower (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    L.coreMass i-(lossN (logScale (originalLog V) L.stopIndex i)+
      lossU (logScale (originalLog V) L.stopIndex i))*Fintype.card V ≤ F.activeMass := by
  have hh := total_active_deficit_payment
    (fun z : L.FoldBoxIndex i => ((L.foldBox i z).vertices.card:ℝ))
    (fun z => vertexMass (L.foldCores i z))
    (fun z => ∑ t,∑ j,(((F.active z).vertices t j).card:ℝ))
    (logScale_active L.initial_log_pos.le L.phase_lower hi) F.deficit
    (by rw [L.fold_box_mass]; exact actual_layer_mass L (by omega))
  rwa [L.fold_core_mass] at hh

theorem activeMass_plus_parent (F : ActualFoldStage12 L i) :
    F.activeMass+vertexMass (advance L.splitter 0 (i+1) [originalPiece G]) ≤
      L.coreMass i+F.batchMass := by
  have hh := sum_le_sum (fun z (_ : z∈(univ:Finset (L.FoldBoxIndex i))) => (F.active z).upper)
  simp only [sum_add_distrib] at hh
  have he (z : L.FoldBoxIndex i) : (∑ r : Fin (L.foldCores i z).length,
      (((L.foldCores i z).get r).vertices.card:ℝ))=vertexMass (L.foldCores i z) :=
    list_sum_get _ (fun R : AssignedPiece V => (R.vertices.card:ℝ))
  simp_rw [he] at hh
  rw [L.fold_box_mass,L.fold_core_mass] at hh
  exact hh

theorem activeMass_upper (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    F.activeMass ≤ L.coreMass i+lossO (logScale (originalLog V) L.stopIndex i)*Fintype.card V := by
  have ha := F.activeMass_plus_parent
  have hb := F.batchMass_le_descendants.trans (L.fold_frontier_mass hi)
  have hp := L.frontier_mass_lower (i+1)
  linarith only [ha,hb,hp]

theorem batchMass_upper (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    F.batchMass ≤ (1+lossO (logScale (originalLog V) L.stopIndex i))*Fintype.card V :=
  F.batchMass_le_descendants.trans (L.fold_frontier_mass hi)

/-- These are precisely the three actual mass inequalities used in the
physical folding ledger, with no abstract mass supplied by a caller. -/
theorem actual_mass_ledger (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) :
    let w := logScale (originalLog V) L.stopIndex i
    L.coreMass i-(lossN w+lossU w)*Fintype.card V ≤ F.activeMass ∧
      F.activeMass ≤ L.coreMass i+lossO w*Fintype.card V ∧
      F.batchMass ≤ (1+lossO w)*Fintype.card V :=
  ⟨F.activeMass_lower hi,F.activeMass_upper hi,F.batchMass_upper hi⟩

end ActualFoldStage12
end
end Cycle12.Even12
