import Cycle12.MajorityExponentialCertificate
import Cycle12.RationalMajorityCertificate

namespace Cycle12
open Real Cycle13

structure RatMajorityInputs where
  lower : ℚ
  mean : ℚ
  correction : ℚ
  mix : ℚ
  expPoint : ℚ
  reciprocal : ℚ
  terms : ℕ

def RatMajorityInputs.Valid (s : RatMajorityInputs) : Prop :=
  2 < s.lower ∧ s.lower^2/((s.lower-1)*(s.lower-2)) ≤ s.correction ∧
    s.mix ≤ 1 ∧ 0 ≤ s.expPoint ∧ 2*s.expPoint ≤ s.mean ∧ 0 ≤ s.reciprocal ∧
    1 ≤ s.reciprocal*ratExpPartial s.expPoint s.terms ∧
    min 1 (s.reciprocal^2*(1+s.mean+s.mean^2/2)) ≤ s.mix

instance (s : RatMajorityInputs) : Decidable s.Valid := by
  unfold RatMajorityInputs.Valid
  infer_instance

theorem rat_majority_inputs_sound (s : RatMajorityInputs) (h : s.Valid) :
    2 < (s.lower:ℝ) ∧ majorityCorrection (s.lower:ℝ) ≤ (s.correction:ℝ) ∧
      min 1 (poissonTailTwo (s.mean:ℝ)) ≤ (s.mix:ℝ) ∧ (s.mix:ℝ) ≤ 1 := by
  obtain ⟨hl,hC,ha1,hx,hqx,hr,hpartial,hbound⟩ := h
  refine ⟨by exact_mod_cast hl,?_,rational_poisson_two_upper s.terms hx hqx hr hpartial hbound,
    by exact_mod_cast ha1⟩
  have hh := (Rat.cast_le (K:=ℝ)).mpr hC
  simpa only [majorityCorrection,Rat.cast_div,Rat.cast_pow,Rat.cast_sub,Rat.cast_mul,
    Rat.cast_one,Rat.cast_ofNat] using hh

/-- Kernel-checked rational inputs and two continuous cubic bounds give
the real majority-cost envelopes at every larger actual minimum degree. -/
theorem rat_majority_inputs_envelopes (s : RatMajorityInputs) (h : s.Valid) {c K : ℝ}
    (hc : 1 ≤ c)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 → majorityCubic 0 (s.correction:ℝ) c rho ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCubic (s.mix:ℝ) ((1-(s.mix:ℝ))*(s.correction:ℝ)) c rho ≤ K) :
    ∀ delta : ℝ, (s.lower:ℝ) ≤ delta → ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection delta*(c-rho)*(3*rho-2*rho^2) ≤ K ∧
      (c-rho)*(min 1 (poissonTailTwo (s.mean:ℝ))+
        (1-min 1 (poissonTailTwo (s.mean:ℝ)))*majorityCorrection delta*(3*rho-2*rho^2)) ≤ K := by
  intro delta hd
  have hs := rat_majority_inputs_sound s h
  exact majority_envelopes_from_lower_degree hs.1 hd hs.2.1 hs.2.2.1 hs.2.2.2 hc hpure hmixed

structure RatMajorityEnvelope where
  sourceRow : ℕ
  kind : ℕ
  inputs : RatMajorityInputs
  c : ℚ
  bound : ℚ

def RatMajorityEnvelope.Sound (s : RatMajorityEnvelope) : Prop :=
  ∀ delta : ℝ, (s.inputs.lower:ℝ) ≤ delta → ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
    majorityCorrection delta*((s.c:ℝ)-rho)*(3*rho-2*rho^2) ≤ (s.bound:ℝ) ∧
    ((s.c:ℝ)-rho)*(min 1 (poissonTailTwo (s.inputs.mean:ℝ))+
      (1-min 1 (poissonTailTwo (s.inputs.mean:ℝ)))*majorityCorrection delta*(3*rho-2*rho^2)) ≤ (s.bound:ℝ)

end Cycle12
