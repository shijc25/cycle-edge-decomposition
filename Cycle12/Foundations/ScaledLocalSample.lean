import Cycle12.Foundations.ScaledVertexSample

namespace Cycle13
open Real Finset SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure LocalCutParameters.ScaleCertificate (C : LocalCutParameters)
    (p q ρ : unitInterval) (n : ℝ) : Prop where
  valid : C.Valid p q ρ
  mark_domain : (p:ℝ)*(q:ℝ) < 1
  residual_lower : (1-(p:ℝ)*(q:ℝ))*(ρ:ℝ) ≤ (p:ℝ)*(1-(q:ℝ))
  cap_pos : 0 < C.cap
  cap_size : C.cap ≤ C.size
  ell_nonneg : 0 ≤ C.ell
  mgf_rate : (p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n ≤ C.θ*C.b
  janson_rate : (p:ℝ)*(q:ℝ)*n ≤ C.jansonRate ρ
  reverse_rate : (p:ℝ)*(q:ℝ)*n ≤ (1-C.ν)^2*C.ell/2

theorem VertexSamplingData.exists_local_sample_above_scale (D : VertexSamplingData)
    (C : LocalCutParameters) {p q ρ : unitInterval} {n m s : ℝ}
    (hD : D.ScaleCertificate p n m) (hC : C.ScaleCertificate p q ρ n)
    (hs : 1 ≤ s) (G : SimpleGraph V)
    (hn : (Fintype.card V:ℝ)=s^2*n) (hm : (Fintype.card G.edgeSet:ℝ)=s^3*m)
    (hmain : GlobalCutProfile G (s*D.main.h)) (hanc : GlobalCutProfile G (s*D.anchor.h))
    (hdeg : ∀ v, s*D.degreeMean ≤ (p:ℝ)*G.degree v)
    (hprofile : (C.scale s).CutProfile G) (hdegree : C.δ=D.main.δ) (hupper : C.upper=D.main.upper)
    (hsum : D.scalarFailureSum p n m+C.failureBound p q ρ n < 1) :
    ∃ U : Finset V, GoodVertexSample G U (s*D.main.δ) (s*D.main.β) D.anchor.L
      (s^2*D.anchor.lower) (s^2*D.main.upper)
      (s^3*(m*(p:ℝ)^2-D.edgeDeviation)) (s^3*(D.incidentFraction*m)) ∧
      LocalSampleCutExpansion G U (s*C.β) C.η := by
  let ρm := residualProbability p (scaledMark D.markMain s hs) (scaledMark_domain hs hD.main_mark_domain)
  let ρa := residualProbability p (scaledMark D.markAnchor s hs) (scaledMark_domain hs hD.anchor_mark_domain)
  let ρl := residualProbability p (scaledMark q s hs) (scaledMark_domain hs hC.mark_domain)
  have hρm := (residual_lower_of_identity_bound hD.main_mark_domain hD.main_residual_lower).trans
    (residualProbability_antitone_mark p D.markMain (scaledMark D.markMain s hs)
      (scaledMark_le _ _ hs) hD.main_mark_domain (scaledMark_domain hs hD.main_mark_domain))
  have hρa := (residual_lower_of_identity_bound hD.anchor_mark_domain hD.anchor_residual_lower).trans
    (residualProbability_antitone_mark p D.markAnchor (scaledMark D.markAnchor s hs)
      (scaledMark_le _ _ hs) hD.anchor_mark_domain (scaledMark_domain hs hD.anchor_mark_domain))
  have hρl := (residual_lower_of_identity_bound hC.mark_domain hC.residual_lower).trans
    (residualProbability_antitone_mark p q (scaledMark q s hs)
      (scaledMark_le _ _ hs) hC.mark_domain (scaledMark_domain hs hC.mark_domain))
  have hbound : (D.scale s hs ρm ρa).failureSum G p+
      (C.scale s).failureBound p (scaledMark q s hs) ρl (Fintype.card V) < 1 := by
    rw [VertexSamplingData.failureSum_eq_scalar,hn,hm]
    exact (add_le_add (D.scalarFailureSum_scale_le hD hs hρm hρa)
      (C.failureBound_mono_scale hC.valid hs hρl hC.ell_nonneg hC.mgf_rate hC.janson_rate hC.reverse_rate)).trans_lt hsum
  obtain ⟨U,hU,hlocal⟩ := (D.scale s hs ρm ρa).exists_sample_with_local G p
    (D.valid_above_scale hD hs G hn hm hmain hanc hdeg) (C.scale s) (scaledMark q s hs) ρl
    (C.valid_scale hC.valid hs hρl hC.cap_pos hC.cap_size)
    (scaledMark_domain hs hC.mark_domain) (residualProbability_identity _ _ _) hprofile
    (by dsimp only [LocalCutParameters.scale,VertexSamplingData.scale,GlobalCutParameters.scale]; rw [hdegree])
    (by dsimp only [LocalCutParameters.scale,VertexSamplingData.scale,GlobalCutParameters.scale]; rw [hupper]) hbound
  refine ⟨U,?_,hlocal⟩
  dsimp only [VertexSamplingData.Good,VertexSamplingData.scale,GlobalCutParameters.scale,AnchorParameters.scale] at hU
  rw [hm] at hU
  convert hU using 1 <;> ring

end
end Cycle13
