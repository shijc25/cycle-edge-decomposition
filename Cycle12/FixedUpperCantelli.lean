import Cycle12.FixedEdgeCantelli

namespace Cycle12
open Finset Cycle13 SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

theorem finite_law_cantelli_upper {Ω : Type*} [Fintype Ω]
    (mu : FiniteLaw Ω) (X : Ω → ℝ) {m v t : ℝ}
    (hmean : mu.expect X=m) (hvar : mu.expect (fun x => (X x-m)^2) ≤ v) (ht : 0 < t) :
    mu.prob (fun x => m+t ≤ X x) ≤ v/(v+t^2) := by
  have hm : mu.expect (fun x => -X x)= -m := by
    simpa only [neg_one_mul,hmean] using mu.expect_const_mul X (-1)
  have hv : mu.expect (fun x => (-X x- -m)^2) ≤ v := by
    have he : (fun x => (-X x- -m)^2)=(fun x => (X x-m)^2) := by funext x; ring
    rwa [he]
  have hh := mu.cantelli_lower (fun x => -X x) hm hv ht
  have he : (fun x => -X x ≤ -m-t)=(fun x => m+t ≤ X x) := by
    funext x
    apply propext
    constructor <;> intro h <;> linarith only [h]
  rwa [he] at hh

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sampling application needs an upper tail for incident edges.
The complement identity supplies its variance, not a change of tail direction. -/
theorem fixed_sample_incident_upper_cantelli (G : SimpleGraph V) (hn : 4 ≤ Fintype.card V)
    {k : ℕ} (hk : k ≤ Fintype.card V) (a : ℝ)
    (ha : (Fintype.card G.edgeSet:ℝ)*
      (1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2) < a) :
    (fixedSizeLaw (univ:Finset V) k).prob (fun S => a ≤ (incidentEdgeCount G S:ℝ)) ≤
      fixedEdgeVarianceCap (Fintype.card V) (Fintype.card V-k:ℕ) (Fintype.card G.edgeSet)/
        (fixedEdgeVarianceCap (Fintype.card V) (Fintype.card V-k:ℕ) (Fintype.card G.edgeSet)+
          (a-(Fintype.card G.edgeSet:ℝ)*(1-fixedChooseRatio (Fintype.card V) (Fintype.card V-k) 2))^2) := by
  have hh := finite_law_cantelli_upper (fixedSizeLaw (univ:Finset V) k)
    (fun S => (incidentEdgeCount G S:ℝ)) (fixed_sample_incident_edge_mean G hk)
    (fixed_sample_incident_variance_bound G hn hk) (sub_pos.mpr ha)
  simpa only [add_sub_cancel] using hh

end
end Cycle12
