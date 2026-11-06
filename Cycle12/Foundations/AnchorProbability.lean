import Cycle12.Foundations.AnchorDeterministic
import Cycle12.Foundations.MarkedExperiment

namespace Cycle13
open Finset SimpleGraph Real
open GlobalCutParameters (side smallSide residualGraph dependencyDegree)
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace AnchorParameters

theorem upper_event_probability (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (hpq : (p:ℝ)*(q:ℝ) < 1) (G : SimpleGraph V) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (C.upperEvent p U T))) ≤
      2*exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*Fintype.card V) :=
  marked_partition_mgf p q hpq (neighborCopyLaw G) side GlobalCutParameters.side_marked
    C.slope C.b C.θ hC.theta_pos hC.mgf_slope

theorem janson_event_probability (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V))
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    (G : SimpleGraph V) (hG : GlobalCutProfile G C.h) :
    (bernoulliSubset p).expect (fun U => (subsetBernoulli U q).expect (fun T =>
      (neighborCopyLaw G T).prob (C.jansonEvent G ρ U T))) ≤
      exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*Fintype.card V) := by
  apply marked_graph_janson_original p q (markProbability p q) ρ rfl hρ
    (neighborCopyLaw G) (residualGraph G) dependencyDegree C.eligible
    hC.fraction_nonneg hC.fraction_le_one
  · intro T _ ξ A hA v w hvw
    exact C.residual_degree hC G T ξ A hA v w hvw
  · intro T hT ξ A hA
    exact C.residual_rate hC G hG T ξ A hT hA

theorem bad_anchor_probability (C : AnchorParameters) {p q ρ : unitInterval}
    (hC : C.Valid p q ρ (Fintype.card V)) (hpq : (p:ℝ)*(q:ℝ) < 1)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ)))
    (G : SimpleGraph V) (hG : GlobalCutProfile G C.h) :
    (bernoulliSubset p).prob (BadAnchorSample G C.δ C.β C.L C.lower C.upper) ≤
    (2*exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*Fintype.card V)+
      exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*Fintype.card V))/C.ω := by
  have hw := bad_anchor_witness_transfer G p q (lower:=C.lower) hC.degree_pos hC.expansion_pos hC.anchor_pos
    hC.anchor_lt_degree hC.error_pos hC.miss_pos hC.mark_degree hC.mark_cap
    hC.witness_pos.le hC.witness_bound
  have hu := marked_two_event_bound p q (neighborCopyLaw G)
    (AnchorCopyWitness G C.δ C.β C.L C.lower C.upper C.err C.miss C.cap)
    (C.upperEvent p) (C.jansonEvent G ρ) (C.witness_implies_tail hC G hG)
    (C.upper_event_probability hC hpq G) (C.janson_event_probability hC hρ G hG)
  apply (le_div_iff₀ hC.witness_pos).mpr
  linarith

end AnchorParameters
end
end Cycle13
