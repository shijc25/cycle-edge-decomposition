import Cycle12.RationalMomentCertificate

namespace Cycle12
open Finset Cycle13 SimpleGraph

structure RatMomentEnvelope where
  sourceRow : ℕ
  inputs : RatMomentCertificate
  edgeProbability : ℚ
  incidentProbability : ℚ

def RatMomentEnvelope.Valid (c : RatMomentEnvelope) : Prop :=
  c.inputs.Valid ∧
  c.inputs.edgeVariance/(c.inputs.edgeVariance+c.inputs.edgeGap^2) ≤ c.edgeProbability ∧
  c.inputs.incidentVariance/(c.inputs.incidentVariance+c.inputs.incidentGap^2) ≤ c.incidentProbability

instance instDecidableRatMomentEnvelopeValid (c : RatMomentEnvelope) : Decidable c.Valid := by
  unfold RatMomentEnvelope.Valid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatMomentEnvelope.Sound (c : RatMomentEnvelope) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {x s : ℝ} {k : ℕ}, 0 < (Fintype.card G.edgeSet:ℝ) → 0 < x →
    (c.inputs.xl:ℝ) ≤ x → x ≤ (c.inputs.xh:ℝ) → (c.inputs.s0:ℝ) ≤ s →
    (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 →
    (Fintype.card G.edgeSet:ℝ)=(Fintype.card V:ℝ)^2/(2*s) →
    k=⌊coverSampleP x*(Fintype.card V:ℝ)⌋₊ →
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => (sampledFinsetEdgeCount G S:ℝ) ≤
        (97/100)*((k:ℝ)/(Fintype.card V:ℝ))^2*(Fintype.card G.edgeSet:ℝ)) ≤
      (c.edgeProbability:ℝ) ∧
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun S => coverSampleV x*(Fintype.card G.edgeSet:ℝ) ≤ (incidentEdgeCount G S:ℝ)) ≤
      (c.incidentProbability:ℝ)

theorem rat_moment_envelope_sound (c : RatMomentEnvelope) (hc : c.Valid) : c.Sound := by
  intro V _ _ G x s k hm hx hxl hxh hs hn hm_eq hk
  obtain ⟨hinternal,hincident⟩ := cover_moment_certificate_sound c.inputs.realCertificate
    (rat_moment_certificate_valid c.inputs hc.1) G hm hx hxl hxh hs hn hm_eq hk
  constructor
  · apply hinternal.trans
    have hh := (Rat.cast_le (K:=ℝ)).mpr hc.2.1
    simpa only [RatMomentCertificate.realCertificate,Rat.cast_div,Rat.cast_add,Rat.cast_pow] using hh
  · apply hincident.trans
    have hh := (Rat.cast_le (K:=ℝ)).mpr hc.2.2
    simpa only [RatMomentCertificate.realCertificate,Rat.cast_div,Rat.cast_add,Rat.cast_pow] using hh

end
end Cycle12
