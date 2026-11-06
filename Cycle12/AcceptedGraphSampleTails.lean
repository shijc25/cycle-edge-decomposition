import Cycle12.CoverProfileCoordinates
import Cycle12.RationalDegreeEnvelope
import Cycle12.RationalMomentEnvelope
import Cycle12.Foundations.BernoulliLogTails

namespace Cycle12
open Finset Real Cycle13 SimpleGraph Cycle13.MixedSample
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem rat_moment_actual_graph_tails (c : RatMomentEnvelope) (hc : c.Valid)
    (G : SimpleGraph V) (hm : 0 < (Fintype.card G.edgeSet:ℝ)) {k : ℕ}
    (hxl : (c.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.inputs.xh:ℝ))
    (hs : (c.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet))
    (hk : k=⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤
        (97/100)*((k:ℝ)/(Fintype.card V:ℝ))^2*(Fintype.card G.edgeSet:ℝ)) ≤
      (c.edgeProbability:ℝ) ∧
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet) ≤ (incidentEdgeCount G S:ℝ)) ≤
      (c.incidentProbability:ℝ) := by
  have hsize := twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  obtain ⟨horder,hmass⟩ := cover_graph_coordinates_exact hn hm
  have hh := rat_moment_envelope_sound c hc G hm (cover_graph_x_pos hn hm) hxl hxh hs horder hmass hk
  have hid : coverSampleV (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card G.edgeSet:ℝ)=
      coverGraphBudget (Fintype.card V) (Fintype.card G.edgeSet) := by
    rw [← cover_graph_budget_identity hn.le hm]
    exact div_mul_cancel₀ _ hm.ne'
  simpa only [hid] using hh

theorem rat_degree_actual_graph_tail (c : RatDegreeEnvelope) (hi : c.inputs.Valid) (hc : c.NumericValid)
    (G : SimpleGraph V) (hm : 0 < (Fintype.card G.edgeSet:ℝ)) {k : ℕ}
    (hxl : (c.inputs.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
    (hxh : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.inputs.xh:ℝ))
    (hs : (c.inputs.s0:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet))
    (hk : k=⌊coverSampleP (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*(Fintype.card V:ℝ)⌋₊)
    (hdegree : ∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ)) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun T => ∃ v, ((neighborsIn G v T).card:ℝ) ≤
        (c.dm:ℝ)*(((k:ℝ)/(Fintype.card V:ℝ))*coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet))) ≤
      (c.probability:ℝ) := by
  have hsize := twice_graph_edges_le_order_sq G
  have hn : (0:ℝ) < Fintype.card V := by nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card V)]
  have hvalid := rat_moment_certificate_valid c.inputs hi
  have hmax : coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ 17/250 := hxh.trans hvalid.sampling.xmax
  have hmean (v : V) : coverScaleMu (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))*
      coverScaleZ (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))
        (sOf (Fintype.card V) (Fintype.card G.edgeSet))
        (((k:ℝ)/(Fintype.card V:ℝ))/coverScaleW (coverGraphX (Fintype.card V) (Fintype.card G.edgeSet))) ≤
      ((k:ℝ)/(Fintype.card V:ℝ))*(neighborsIn G v univ).card := by
    rw [neighborsIn_univ_card]
    exact cover_delete_threshold_gives_sample_mean hn hm (by positivity) hmax (hdegree v)
  have hh := rat_degree_envelope_sound c hi hc G (cover_graph_x_pos hn hm) hxl hxh hs
    (cover_graph_coordinates_exact hn hm).1 hk hmean
  simpa only [cover_graph_z_eq_sampling_expansion hn hm hmax] using hh

end
end Cycle12
