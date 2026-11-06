import Cycle12.Foundations.LocalCutDeterministic
import Cycle12.Foundations.MarkedExperiment
import Cycle12.Foundations.MarkedLabelOriginal

/-! The complete local-cut probability estimate for actual finite
simple graphs. The scalar certificate is explicit; no successful-event
conditioning is used to assert residual independence. -/
namespace Cycle13
open Finset SimpleGraph Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace LocalCutParameters

theorem upper_event_probability (C : LocalCutParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ) (hpq : (p:ℝ)*(q:ℝ) < 1) (G : SimpleGraph V) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (C.upperEvent p U T))) ≤
      exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*Fintype.card V) :=
  label_aware_mgf p q hpq (neighborCopyLaw G) side side_marked
    C.slope C.b C.θ hC.theta_pos hC.mgf_slope

theorem reverse_event_probability (C : LocalCutParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ))) (G : SimpleGraph V) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (C.reverseEvent U T))) ≤
      exp (-(1-C.ν)^2*C.ell/2+(p:ℝ)*(q:ℝ)*Fintype.card V) :=
  reverse_label_fraction_original p q (markProbability p q) ρ rfl hρ
    (neighborCopyLaw G) side hC.reverse_nonneg hC.reverse_le_one hC.reverse_mean

theorem janson_event_probability (C : LocalCutParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    (G : SimpleGraph V) (hG : C.CutProfile G) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (C.jansonEvent G ρ U T))) ≤
      exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*Fintype.card V) := by
  apply marked_graph_janson_original p q (markProbability p q) ρ rfl hρ
    (neighborCopyLaw G) (C.residualGraph G) C.dependencyDegree C.eligible
    hC.fraction_nonneg hC.fraction_le_one
  · intro T _ ξ A hA v w hvw
    exact C.residual_degree hC G T ξ A hA v w hvw
  · intro T hT ξ A hA
    exact C.residual_rate hC G hG T ξ A hT hA

theorem local_bad_cut_probability (C : LocalCutParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ) (hpq : (p:ℝ)*(q:ℝ) < 1)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    (G : SimpleGraph V) (hG : C.CutProfile G) :
    (bernoulliSubset p).prob (BadCutWithin G C.δ C.β C.upper
      (fun U A => (A.card:ℝ) ≤ C.η*U.card)) ≤
    (exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*Fintype.card V)+
      exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*Fintype.card V)+
      exp (-(1-C.ν)^2*C.ell/2+(p:ℝ)*(q:ℝ)*Fintype.card V))/C.ω := by
  have hw := bad_cut_within_witness_transfer G p q
    (fun U A => (A.card:ℝ) ≤ C.η*U.card) hC.degree_pos hC.mark_degree
    hC.error_pos hC.mark_cap hC.witness_pos.le hC.witness_bound
  have hu := marked_three_event_bound p q (neighborCopyLaw G)
    (CutWitnessWithin G C.δ C.β C.err C.upper C.cap (fun U A => (A.card:ℝ) ≤ C.η*U.card))
    (C.upperEvent p) C.reverseEvent (C.jansonEvent G ρ)
    (C.witness_implies_tail hC G hG)
    (C.upper_event_probability hC hpq G) (C.reverse_event_probability hC hρ G)
    (C.janson_event_probability hC hρ G hG)
  apply (le_div_iff₀ hC.witness_pos).mpr
  linarith

end LocalCutParameters
end
end Cycle13
