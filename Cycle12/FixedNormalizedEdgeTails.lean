import Cycle12.FixedGraphNormalizedVariance
import Cycle12.NormalizedCantelli
import Cycle12.CoverMeanBudget

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_internal_edge_tail_budget (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card V)
    {p s nlo klo alpha v gap : ℝ} (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (hs : 0 < s)
    (hp : p=(k:ℝ)/(Fintype.card V:ℝ))
    (hm_eq : (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s))
    (hnlo : 1 < nlo) (hnn : nlo ≤ Fintype.card V) (hklo : 0 < klo) (hkk : klo ≤ k)
    (hv : 2*(1-p)*(s-1)/(p*(Fintype.card V:ℝ))*finiteOrderVarianceFactor (Fintype.card V) ≤ v)
    (hgap : 0 < gap) (hgapbound : gap ≤ (1-alpha)-1/(klo*(1-1/nlo))) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤ alpha*p^2*(Fintype.card G.edgeSet:ℝ)) ≤
      v/(v+gap^2) := by
  have hvar := fixed_graph_internal_normalized_variance G hn hk1 hk hm hs hp hm_eq
  have hn0 : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp0 : 0 < p := by rw [hp]; positivity
  have hscale : 0 < p^2*(Fintype.card G.edgeSet:ℝ) := by positivity
  have hgapactual := cover_internal_gap_box (Fintype.card V) k hnlo hnn hklo hkk hm.le (alpha:=alpha)
  rw [← hp] at hgapactual
  have hgapmul := mul_le_mul_of_nonneg_right hgapbound hscale.le
  have hvarmul := mul_le_mul_of_nonneg_right hv (sq_nonneg (p^2*(Fintype.card G.edgeSet:ℝ)))
  apply normalized_cantelli_lower (fixedSizeLaw (univ:Finset V) k)
    (fun S => (sampledFinsetEdgeCount G S:ℝ)) (fixed_sample_edge_mean G hk)
    hvar hscale hgap hvarmul
  nlinarith only [hgapmul,hgapactual]

theorem fixed_incident_edge_tail_budget (G : SimpleGraph V)
    (hn : 4 ≤ Fintype.card V) {k : ℕ} (hk : k < Fintype.card V)
    {p s w target v gap : ℝ} (hm : 0 < (Fintype.card G.edgeSet:ℝ)) (hs : 0 < s) (hw : 0 < w)
    (hp : p=(k:ℝ)/(Fintype.card V:ℝ))
    (hm_eq : (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s))
    (hv : 2*p*(1-p)^3*(s-1)/(w^2*(Fintype.card V:ℝ))*finiteOrderVarianceFactor (Fintype.card V) ≤ v)
    (hgap : 0 < gap)
    (hgapbound : gap*w ≤ target-(1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2)) :
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => target*(Fintype.card G.edgeSet:ℝ) ≤ (incidentEdgeCount G S:ℝ)) ≤
      v/(v+gap^2) := by
  have hvar := fixed_graph_incident_normalized_variance G hn hk hm hs hw hp hm_eq
  have hscale : 0 < w*(Fintype.card G.edgeSet:ℝ) := mul_pos hw hm
  have hgapmul := mul_le_mul_of_nonneg_right hgapbound hm.le
  have hvarmul := mul_le_mul_of_nonneg_right hv (sq_nonneg (w*(Fintype.card G.edgeSet:ℝ)))
  apply normalized_cantelli_upper (fixedSizeLaw (univ:Finset V) k)
    (fun S => (incidentEdgeCount G S:ℝ)) (fixed_sample_incident_edge_mean G hk.le)
    hvar hscale hgap hvarmul
  nlinarith only [hgapmul]

end
end Cycle12
