import Cycle12.FixedAnchorUpper

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Actual fixed-size external anchoring failure, with the majority
witness and its two distinct error charges fully proved. -/
theorem fixed_anchor_failure_bound (G : SimpleGraph V) {N t : ℕ}
    (hN : N ≤ Fintype.card V) (ht : t ≤ N) (htD : t < Fintype.card V)
    {z dm beta L ew miss theta ell intercept raw pLower ce nu tail : ℝ}
    (hz : 0 < z) (hdm : 0 < dm) (hb : 0 < beta) (hL : 0 < L) (hew : 0 ≤ ew)
    (hmiss1 : miss < 1) (htheta : 0 < theta) (hscale : 0 < ell/theta) (hce : 0 < ce)
    (hceFirst : ce ≤ 1-miss)
    (hceSecond : ce*min (1-pLower) ((1-raw)/(1-miss)) ≤ raw)
    (hNlower : pLower*Fintype.card V ≤ (N:ℝ))
    (hpop : (ell/theta)*(raw*Fintype.card V)+intercept ≤
      (N:ℝ)/2-(ew+2)*L*Fintype.card V/(dm*z))
    (hnu : nu ≤ max (min ((1-miss)*((beta*z)*(dm*z-L)/L)) (raw*Fintype.card V))
      ((dm*z-L-intercept)/((ell/theta)+(ew+2)*L/((dm*z)*ce))))
    (hmgf : 1-((N-t:ℕ):ℝ)/(Fintype.card V-t)+
      ((N-t:ℕ):ℝ)/(Fintype.card V-t)*exp theta ≤ exp ell)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : (p:ℝ) ≤ 1/2)
    (hmean : ((Fintype.card V-t:ℕ):ℝ)*(p:ℝ)=((N-t:ℕ):ℝ)) (htail : 0 ≤ tail)
    {voteLambda K Kfull omega : ℝ} (hNpos : 0 < N) (hewPos : 0 < ew) (hmiss : 0 < miss)
    (hdelta : 2 < dm*z) (hvotelambda : 3 ≤ voteLambda)
    (hvotemean : voteLambda ≤ ((t:ℝ)/N)*(dm*z)) (hK : 0 ≤ K)
    (hpure : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      majorityCorrection (dm*z)*(1-r)*(3*r-2*r^2) ≤ K)
    (hmixed : ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      (1-r)*(min 1 (poissonTailTwo voteLambda)+
        (1-min 1 (poissonTailTwo voteLambda))*majorityCorrection (dm*z)*(3*r-2*r^2)) ≤ K)
    (hKfull : 1 ≤ Kfull) (hcor : majorityCorrection (dm*z)*(9/8) ≤ Kfull)
    (homega : 0 < omega)
    (hwitness : omega ≤ 1-(2*K+(dm/beta)*exp (-voteLambda))/ew-
      (Kfull*L/(dm*z)+exp (-voteLambda))/miss)
    (lambda M fraction : Finset V → Finset V → (V → Finset V) → ℝ)
    (hvalid : ∀ T : Finset V, T.card=t → ∀ A⊆T, ∀ xi,
      nu ≤ ((fixedMajoritySmallSide T A xi).card:ℝ) →
      RoundedCutLabelValid G (fixedMajoritySmallSide T A xi) T p
        (lambda T A xi) (M T A xi) (fraction T A xi) tail ∧
      ((1+ew)*L/ce)*(fixedMajoritySmallSide T A xi).card ≤
        fraction T A xi*(M T A xi*(p:ℝ)^2)) :
    (fixedSizeLaw (univ:Finset V) N).prob (FixedAnchorFailure G N z dm beta L) ≤
      (2*exp (-theta*intercept)*(1+exp (theta-ell))^t+(2:ℝ)^t*tail)/omega := by
  have hlower := fixed_anchor_bad_cut_transfer G hNpos ht hz hdm hb hL hdelta
    hvotelambda hvotemean hK hpure hmixed hewPos hmiss hKfull hcor homega.le hwitness
  have hupper := fixed_anchor_witness_upper G hN ht htD hz hdm hb hL hew hmiss1 htheta hscale
    hce hceFirst hceSecond hNlower hpop hnu hmgf p hp0 hp hmean htail lambda M fraction hvalid
  apply (le_div_iff₀ homega).mpr
  simpa only [mul_comm] using hlower.trans hupper

end
end Cycle12
