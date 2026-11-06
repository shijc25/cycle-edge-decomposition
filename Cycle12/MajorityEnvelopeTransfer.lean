import Cycle12.MajorityCubicEnvelope
import Cycle12.ThreeVoteBound
import Cycle12.FixedSamplePoissonTail

namespace Cycle12
noncomputable section

/-- Both endpoints in the low-vote mixing parameter are needed: the
mixture can either increase or decrease with that parameter. -/
theorem majority_envelope_transfer {C Cmax a amax c K rho : ℝ}
    (hC : C ≤ Cmax) (ha0 : 0 ≤ a) (ha : a ≤ amax) (ha1 : amax ≤ 1)
    (hc : 1 ≤ c) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
    (hpure : majorityCubic 0 Cmax c rho ≤ K)
    (hmixed : majorityCubic amax ((1-amax)*Cmax) c rho ≤ K) :
    C*(c-rho)*(3*rho-2*rho^2) ≤ K ∧
      (c-rho)*(a+(1-a)*C*(3*rho-2*rho^2)) ≤ K := by
  let f := 3*rho-2*rho^2
  have hf : 0 ≤ f := by
    have hh := mul_nonneg hr0 (show 0 ≤ 3-2*rho by linarith only [hr1])
    dsimp only [f]
    nlinarith only [hh]
  have hcr : 0 ≤ c-rho := by linarith only [hc,hr1]
  have hCf := mul_le_mul_of_nonneg_right hC hf
  have hCpure := mul_le_mul_of_nonneg_left hCf hcr
  have hCmix := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hCf (show 0 ≤ 1-a by linarith only [ha,ha1])) hcr
  change C*(c-rho)*f ≤ K ∧ (c-rho)*(a+(1-a)*C*f) ≤ K
  change (c-rho)*(0+Cmax*f) ≤ K at hpure
  change (c-rho)*(amax+((1-amax)*Cmax)*f) ≤ K at hmixed
  constructor
  · nlinarith only [hCpure,hpure]
  · by_cases hd : 0 ≤ 1-Cmax*f
    · have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hd) hcr
      nlinarith only [hCmix,hmixed,hh]
    · have hh := mul_nonpos_of_nonneg_of_nonpos ha0 (le_of_not_ge hd)
      have hhh := mul_nonpos_of_nonneg_of_nonpos hcr hh
      nlinarith only [hCmix,hpure,hhh]

theorem majority_envelopes_from_lower_degree {delta lower c K Cmax amax lambda : ℝ}
    (hlower : 2 < lower) (hdelta : lower ≤ delta)
    (hC : majorityCorrection lower ≤ Cmax)
    (ha : min 1 (poissonTailTwo lambda) ≤ amax) (ha1 : amax ≤ 1) (hc : 1 ≤ c)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 → majorityCubic 0 Cmax c rho ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCubic amax ((1-amax)*Cmax) c rho ≤ K) :
    ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection delta*(c-rho)*(3*rho-2*rho^2) ≤ K ∧
      (c-rho)*(min 1 (poissonTailTwo lambda)+
        (1-min 1 (poissonTailTwo lambda))*majorityCorrection delta*(3*rho-2*rho^2)) ≤ K := by
  intro rho hr0 hr1
  have hCactual := (majority_correction_antitone hlower hdelta).trans hC
  have htail : 0 ≤ min 1 (poissonTailTwo lambda) := by
    apply le_min (by norm_num)
    unfold poissonTailTwo
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith [sq_nonneg (lambda+1)]
  exact majority_envelope_transfer hCactual htail ha ha1 hc hr0 hr1 (hpure rho hr0 hr1) (hmixed rho hr0 hr1)

end
end Cycle12
