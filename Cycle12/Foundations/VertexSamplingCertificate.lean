import Cycle12.Foundations.SampleSuccess
import Cycle12.Foundations.BernoulliLogTails

namespace Cycle13
open Finset SimpleGraph Real
open OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def GlobalCutParameters.failureBound (C : GlobalCutParameters)
    (p q ρ : unitInterval) (n : ℝ) : ℝ :=
  (2*exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n)+
    exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n))/C.ω

def AnchorParameters.failureBound (C : AnchorParameters)
    (p q ρ : unitInterval) (n : ℝ) : ℝ :=
  (2*exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n)+
    exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n))/C.ω

def LocalCutParameters.failureBound (C : LocalCutParameters)
    (p q ρ : unitInterval) (n : ℝ) : ℝ :=
  (exp (-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n)+
    exp (-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n)+exp (-(1-C.ν)^2*C.ell/2+(p:ℝ)*(q:ℝ)*n))/C.ω

def sampleEdgeVarianceBound (G : SimpleGraph V) (p : unitInterval) : ℝ :=
  (Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2+
    2*(Fintype.card G.edgeSet:ℝ)*Fintype.card V*(p:ℝ)^3*(1-(p:ℝ))

def sampleEdgeFailureBound (G : SimpleGraph V) (p : unitInterval) (t : ℝ) : ℝ :=
  sampleEdgeVarianceBound G p/(sampleEdgeVarianceBound G p+t^2)

def incidentFailureBound (G : SimpleGraph V) (p : unitInterval) (v : ℝ) : ℝ :=
  exp (-((Fintype.card G.edgeSet:ℝ)/Fintype.card V)*(v-2*(p:ℝ)+(p:ℝ)^2)^2/
    ((1-(p:ℝ))*(4*(p:ℝ)+2*(v-2*(p:ℝ)+(p:ℝ)^2)/3)))

structure VertexSamplingData where
  main : GlobalCutParameters
  anchor : AnchorParameters
  markMain : unitInterval
  residualMain : unitInterval
  markAnchor : unitInterval
  residualAnchor : unitInterval
  degreeMean : ℝ
  edgeDeviation : ℝ
  incidentFraction : ℝ

namespace VertexSamplingData

structure Valid (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval) : Prop where
  main_valid : D.main.Valid p D.markMain D.residualMain (Fintype.card V)
  anchor_valid : D.anchor.Valid p D.markAnchor D.residualAnchor (Fintype.card V)
  main_profile : GlobalCutProfile G D.main.h
  anchor_profile : GlobalCutProfile G D.anchor.h
  main_mark_domain : (p:ℝ)*(D.markMain:ℝ) < 1
  anchor_mark_domain : (p:ℝ)*(D.markAnchor:ℝ) < 1
  main_residual : (1-(p:ℝ)*(D.markMain:ℝ))*(D.residualMain:ℝ)=(p:ℝ)*(1-(D.markMain:ℝ))
  anchor_residual : (1-(p:ℝ)*(D.markAnchor:ℝ))*(D.residualAnchor:ℝ)=(p:ℝ)*(1-(D.markAnchor:ℝ))
  match_degree : D.anchor.δ=D.main.δ
  match_expansion : D.anchor.β=D.main.β
  match_order : D.anchor.upper=D.main.upper
  order_lower_pos : 0 < D.anchor.lower
  order_lower_mean : D.anchor.lower ≤ (p:ℝ)*Fintype.card V
  order_upper_mean : (p:ℝ)*Fintype.card V ≤ D.main.upper
  degree_mean_pos : 0 < D.degreeMean
  degree_threshold : D.main.δ ≤ D.degreeMean
  degree_mean : ∀ v, D.degreeMean ≤ (p:ℝ)*G.degree v
  edge_deviation_pos : 0 < D.edgeDeviation
  edge_count_pos : 0 < (Fintype.card G.edgeSet:ℝ)
  sample_lt_one : (p:ℝ) < 1
  incident_threshold : 2*(p:ℝ)-(p:ℝ)^2 < D.incidentFraction

def failureSum (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval) : ℝ :=
  exp (-poissonRate ((p:ℝ)*Fintype.card V) D.anchor.lower)+
  exp (-poissonRate ((p:ℝ)*Fintype.card V) D.main.upper)+
  (Fintype.card V:ℝ)*exp (-poissonRate D.degreeMean D.main.δ)+
  D.main.failureBound p D.markMain D.residualMain (Fintype.card V)+
  D.anchor.failureBound p D.markAnchor D.residualAnchor (Fintype.card V)+
  sampleEdgeFailureBound G p D.edgeDeviation+
  incidentFailureBound G p D.incidentFraction

def Good (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval) (U : Finset V) : Prop :=
  GoodVertexSample G U D.main.δ D.main.β D.anchor.L D.anchor.lower D.main.upper
    ((Fintype.card G.edgeSet:ℝ)*(p:ℝ)^2-D.edgeDeviation)
    (D.incidentFraction*(Fintype.card G.edgeSet:ℝ))

theorem exists_sample_avoiding (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval)
    (hD : D.Valid G p) (extraBad : Finset V→Prop) {bExtra : ℝ}
    (hExtra : (bernoulliSubset p).prob extraBad ≤ bExtra)
    (hsum : D.failureSum G p+bExtra < 1) :
    ∃ U : Finset V, D.Good G p U ∧ ¬extraBad U := by
  have hn : 0 < (Fintype.card V:ℝ) :=
    (mul_pos (by norm_num : (0:ℝ) < 9) hD.main_valid.scale_pos).trans_le hD.main_valid.order_scale
  have hμ : 0 < (p:ℝ)*Fintype.card V := mul_pos hD.main_valid.p_pos hn
  have hdeg : ∀ v, G.degree v ≤ Fintype.card V := fun v => (G.degree_lt_card_verts v).le
  apply exists_sample_of_failure_bounds G p extraBad
    (bernoulliSubset_card_lower_log p hμ hD.order_lower_pos hD.order_lower_mean)
    (bernoulliSubset_card_upper_log p hμ hD.order_upper_mean)
    (bernoulliSubset_all_degrees_log G p hD.degree_mean_pos hD.main_valid.degree_pos
      hD.degree_threshold hD.degree_mean)
    (D.main.global_bad_cut_probability hD.main_valid hD.main_mark_domain hD.main_residual G hD.main_profile)
    (bAnchor:=D.anchor.failureBound p D.markAnchor D.residualAnchor (Fintype.card V))
    (bEdge:=sampleEdgeFailureBound G p D.edgeDeviation)
    (bIncident:=incidentFailureBound G p D.incidentFraction) ?_ ?_ ?_ hExtra hsum
  · have hh := D.anchor.bad_anchor_probability hD.anchor_valid hD.anchor_mark_domain
      hD.anchor_residual G hD.anchor_profile
    simpa only [hD.match_degree,hD.match_expansion,hD.match_order,
      AnchorParameters.failureBound] using hh
  · exact (FiniteLaw.prob_mono _ (fun U h => h.le)).trans
      (sampledEdgeCount_cantelli G p hdeg hD.edge_deviation_pos)
  · exact (FiniteLaw.prob_mono _ (fun U h => h.le)).trans
      (incidentEdgeCount_freedman_fraction G p hD.main_valid.p_pos hD.sample_lt_one hn
        hD.edge_count_pos hD.incident_threshold (fun v => by exact_mod_cast hdeg v))

theorem exists_sample (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval)
    (hD : D.Valid G p) (hsum : D.failureSum G p < 1) : ∃ U : Finset V, D.Good G p U := by
  have hh := D.exists_sample_avoiding G p hD (fun _ => False) (bExtra:=0)
    (by simp only [FiniteLaw.prob,ite_false,FiniteLaw.expect_const,le_refl]) (by simpa using hsum)
  exact hh.imp (fun _ h => h.1)

theorem exists_sample_with_local (D : VertexSamplingData) (G : SimpleGraph V) (p : unitInterval)
    (hD : D.Valid G p) (C : LocalCutParameters) (q ρ : unitInterval)
    (hC : C.Valid p q ρ) (hpq : (p:ℝ)*(q:ℝ) < 1)
    (hρ : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ))) (hG : C.CutProfile G)
    (hdegree : C.δ=D.main.δ) (hupper : C.upper=D.main.upper)
    (hsum : D.failureSum G p+C.failureBound p q ρ (Fintype.card V) < 1) :
    ∃ U : Finset V, D.Good G p U ∧ LocalSampleCutExpansion G U C.β C.η := by
  obtain ⟨U,hU,hlocal⟩ := D.exists_sample_avoiding G p hD
    (BadCutWithin G C.δ C.β C.upper (fun U A => (A.card:ℝ) ≤ C.η*U.card))
    (C.local_bad_cut_probability hC hpq hρ G hG) hsum
  refine ⟨U,hU,?_⟩
  apply sample_local_expansion_of_not_bad G U (by simpa only [hupper] using hU.order_upper)
    (fun v _ => by simpa only [hdegree] using hU.neighbors v) hlocal

end VertexSamplingData
end
end Cycle13
