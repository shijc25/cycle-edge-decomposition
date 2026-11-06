import Cycle12.FixedGlobalSplitUpper

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The full actual fixed-size expansion-failure bound with two label
regimes. Deterministic graph and scalar certificates remain explicit. -/
theorem fixed_global_split_expansion_failure_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta tau q theta ell err nu rho cutoff etaSmall etaLarge : ℝ}
    (hz : 0 < z) (hb : 0 < beta) (hbt : beta < tau) (hbd : beta < dm)
    (htheta : 0 < theta) (hscale : 0 < ell/theta) (hnu : 0 < nu)
    (hr : 0 < rho) (hrhalf : rho ≤ 1/2) (heS : 0 ≤ etaSmall) (heL : 0 ≤ etaLarge)
    (hnuBound : nu ≤
      (max (dm-tau) ((1-(tau-beta)/(tau+(dm-beta)/2))*(dm-beta))*z-err)/(ell/theta))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (hlabelBudget : (exp 1-1)*((t:ℝ)/N)*
      (((ell/theta)*cutoff+err)/(1-(tau-beta)/(tau+(dm-beta)/2)))+q ≤ rho*t)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ))
    {voteLambda K omega : ℝ} (hdelta : 2 < dm*z) (hvotelambda : 3 ≤ voteLambda)
    (hvotemean : voteLambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection (dm*z)*(1+tau/dm-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      (1+tau/dm-rho)*(min 1 (poissonTailTwo voteLambda)+
        (1-min 1 (poissonTailTwo voteLambda))*majorityCorrection (dm*z)*(3*rho-2*rho^2)) ≤ K)
    (homega : 0 < omega)
    (hwitness : omega ≤ 1-(2*K*beta+(dm+tau)*exp (-voteLambda))/(tau-beta)-exp (-q))
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T p
        (lambda T A xi) (M T A xi) (fraction T A xi)
        (if ((fixedMajoritySmallSide T A xi).card:ℝ) ≤ cutoff then etaSmall else etaLarge) ∧
      tau*z*((ell/theta)*(fixedMajoritySmallSide T A xi).card+err) ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2)) :
    (fixedSizeLaw (univ:Finset V) N).prob (FixedExpansionFailure G univ N z dm beta) ≤
      (2*exp (-theta*err)*(1+exp (theta-ell))^t+
        (exp ((t:ℝ)*binEntropy rho)*etaSmall+(2:ℝ)^t*etaLarge))/omega := by
  have hlower := fixed_majority_strong_bad_cut_transfer G (univ:Finset V) ht hz
    (hb.trans hbd) hb hbt hbd hdelta hvotelambda hvotemean hK hpure hmixed homega.le hwitness
  have hupper := fixed_global_split_witness_upper G hN ht htD (q:=q) hz hb hbt hbd htheta hscale hnu
    hr hrhalf heS heL hnuBound hmgf hlabelBudget p hp0 hp hmean lambda M fraction hvalid
  apply (le_div_iff₀ homega).mpr
  simpa only [mul_comm] using hlower.trans hupper

end
end Cycle12
