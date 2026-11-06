import Cycle12.FixedRestrictedUpper

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]

/-- Closed restricted-cut failure bound for the original fixed-size sample.
The inputs after the witness envelopes are deterministic graph and scalar
certificates; no probabilistic inequality is assumed. -/
theorem fixed_restricted_failure_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta err eta q theta ell intercept nu size reverseMean reverseFraction : ℝ}
    (hz : 0 < z) (hbe : 0 ≤ beta+err) (hc : (err+2*beta)/dm < 1)
    (htheta : 0 < theta) (hscale : 0 < ell/theta)
    (hnuBound : nu ≤ (((1-(err+2*beta)/dm)*(dm-beta))*z-intercept)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (hrMean : 0 < reverseMean) (hr0 : 0 < reverseFraction) (hr1 : reverseFraction < 1)
    (hrmean : reverseMean ≤ (((N-t:ℕ):ℝ)/(Fintype.card V-t:ℕ))*(size-t))
    (hlocal : (1+(err+2*beta)/dm)*eta*N < reverseFraction*reverseMean)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {voteLambda K omega : ℝ} (hdm : 0 < dm) (herr : 0 < err)
    (hdelta : 2 < dm*z) (hvotelambda : 3 ≤ voteLambda)
    (hvotemean : voteLambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      majorityCorrection (dm*z)*(1-r)*(3*r-2*r^2) ≤ K)
    (hmixed : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      (1-r)*(min 1 (poissonTailTwo voteLambda)+
        (1-min 1 (poissonTailTwo voteLambda))*majorityCorrection (dm*z)*(3*r-2*r^2)) ≤ K)
    (homega : 0 < omega)
    (hwitness : omega ≤ 1-(2*K*beta+dm*exp (-voteLambda))/err-exp (-q))
    (lambda M fraction : I → Finset V → Finset V → (V → Finset V) → ℝ)
    (eligible : I → Finset V → Finset V → (V → Finset V) → Prop)
    (rho tail : I → ℝ) (hrho : ∀ i, 0 < rho i) (htail : ∀ i, 0 ≤ tail i)
    (hcover : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySide univ T A xi).card:ℝ) →
      ((fixedMajoritySide univ T A xi).card:ℝ) < size → ∃ i, eligible i T A xi)
    (hvalid : ∀ i T, T.card=t → ∀ A⊆T, ∀ xi, eligible i T A xi →
      RoundedCutLabelValid G (fixedMajoritySide univ T A xi) T p
        (lambda i T A xi) (M i T A xi) (fraction i T A xi) (tail i) ∧
      (beta+err)*z*(((ell/theta)*(fixedMajoritySide univ T A xi).card+intercept)/
        (1-(err+2*beta)/dm)) ≤ fraction i T A xi*(M i T A xi*(p:ℝ)^2) ∧
      (exp 1-1)*((t:ℝ)/N)*
        (((ell/theta)*(fixedMajoritySide univ T A xi).card+intercept)/(1-(err+2*beta)/dm))+q ≤ rho i*t) :
    (fixedSizeLaw (univ:Finset V) N).prob
      (FixedRestrictedCutFailure G univ N z dm beta eta) ≤
      (2*exp (-theta*intercept)*(1+exp (theta-ell))^t+
        (2:ℝ)^t*exp (-(1-reverseFraction)^2*reverseMean/2)+
        ∑ i, exp ((t:ℝ)*cappedLabelEntropy (rho i))*tail i)/omega := by
  have hlower := fixed_restricted_bad_cut_transfer G (univ:Finset V) (eta:=eta) ht hz hdm herr hc
    hdelta hvotelambda hvotemean hK hpure hmixed homega.le hwitness
  have hupper := fixed_restricted_witness_upper G hN ht htD (q:=q) hz hbe hc
    htheta hscale hnuBound hmgf hrMean hr0 hr1 hrmean hlocal p hp0 hp hmean
    lambda M fraction eligible rho tail hrho htail hcover hvalid
  apply (le_div_iff₀ homega).mpr
  simpa only [mul_comm] using hlower.trans hupper

end
end Cycle12
