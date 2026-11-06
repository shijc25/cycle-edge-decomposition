import Cycle12.ScaleSchedule12
import Cycle12.SupportedEdges
import Cycle12.LayerCyclePayment
import Cycle12.LayerRemainder

namespace Cycle12.Global12
open SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def originalPiece (G : SimpleGraph V) : AssignedPiece V :=
  ⟨univ,G,fun _ _ _ => ⟨Finset.mem_univ _,Finset.mem_univ _⟩⟩

def originalLog (V : Type) [Fintype V] : ℝ := logb 2 (Fintype.card V)

structure ScaleLayers12 (G : SimpleGraph V) where
  stopIndex : ℕ
  phase_lower : wA≤theta2^stopIndex*originalLog V
  phase_upper : theta2^stopIndex*originalLog V<wA/theta2
  splitter : SplitSystem V
  bounds : ∀ i<stopIndex+3, ∀ P∈advance splitter 0 i [originalPiece G],
    EntropyStageBounds (splitter i P)
      ((2:ℝ)^(logScale (originalLog V) stopIndex i))
      ((2:ℝ)^((1+eps)*logScale (originalLog V) stopIndex i))
      ((2:ℝ)^(rho*logScale (originalLog V) stopIndex i))
      ((2:ℝ)^(s*logScale (originalLog V) stopIndex i))
  degrees : ∀ i ≤ stopIndex+3, ∀ P∈advance splitter 0 i [originalPiece G],
    2*(edgeCount P.graph:ℝ)≤(2:ℝ)^(logScale (originalLog V) stopIndex i)*P.vertices.card

theorem exists_actual_scale_layers (G : SimpleGraph V) (hn : 0<Fintype.card V)
    (hlarge : wA≤originalLog V) : Nonempty (ScaleLayers12 G) := by
  have hwA : 0<wA := by norm_num [wA]
  have hX : 0≤originalLog V := (hwA.trans_le hlarge).le
  obtain ⟨k,hphase,hupper⟩ := exists_geometric_stop_phase hwA hlarge
    (show 0<theta2 by norm_num [theta2]) (show theta2<1 by norm_num [theta2])
  let d := scaleData (originalLog V) k hX hphase
  obtain ⟨sp,hsp⟩ := exists_variable_entropy_splitter (V:=V) d
  have hpow : (2:ℝ)^(originalLog V)=Fintype.card V :=
    Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr hn)
  have hdeg : ∀ P∈[originalPiece G], 2*(edgeCount P.graph:ℝ)≤d.degree 0*P.vertices.card := by
    intro P hP
    obtain rfl := List.mem_singleton.mp hP
    have he := supported_edge_count_le_square G univ (originalPiece G).supported
    have hi : d.degree 0=(Fintype.card V:ℝ) := by
      change (2:ℝ)^(threeRateLog theta0 theta1 theta2 (originalLog V) k 0)=Fintype.card V
      rw [three_rate_initial,hpow]
    rw [hi]
    simp only [originalPiece,Finset.card_univ] at he ⊢
    nlinarith only [he]
  refine ⟨⟨k,hphase,hupper,sp,?_,?_⟩⟩
  · intro i hi
    have hh := variable_advance_entropy_bounds d sp hsp 0 i [originalPiece G] hdeg
      (fun j hj => by change 0+j<k+3; omega)
    simpa only [Nat.zero_add,d,scaleData] using hh
  · intro i hi
    have hh := variable_advance_degree d sp hsp 0 i [originalPiece G] hdeg
      (fun j hj => by change 0+j<k+3; omega)
    simpa only [Nat.zero_add,d,scaleData] using hh

theorem ScaleLayers12.exact_partition {G : SimpleGraph V} (L : ScaleLayers12 G) (i : ℕ) :
    GraphPartition G
      (pastCycles L.splitter 0 i [originalPiece G] ++
        (pastPieces L.splitter 0 i [originalPiece G]).map AssignedPiece.graph ++
          (advance L.splitter 0 i [originalPiece G]).map AssignedPiece.graph) :=
  past_partition L.splitter 0 i (originalPiece G)

theorem ScaleLayers12.stopped_partition {G : SimpleGraph V} (L : ScaleLayers12 G) (i : ℕ) :
    GraphPartition G
      (pastCycles L.splitter 0 i [originalPiece G] ++
        (pastPieces L.splitter 0 i [originalPiece G]).map AssignedPiece.graph ++
          [graphUnion ((advance L.splitter 0 i [originalPiece G]).map AssignedPiece.graph)]) :=
  stopped_layer_partition L.splitter 0 i (originalPiece G)

end
end Cycle12.Global12
