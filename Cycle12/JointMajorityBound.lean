import Cycle12.ThreeVoteBound
import Cycle12.JointClassifierExpectation

namespace Cycle12
open Real
noncomputable section

/-- Endpoint bounds for the two cubic joint-cost polynomials imply a
uniform bound for every actual proportion of one- or two-vote outcomes. -/
theorem majority_joint_mixture_bound {rho c C a a0 K p : ℝ}
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (hc : 1 ≤ c)
    (ha : 0 ≤ a) (haa : a ≤ a0)
    (hp : p ≤ a*rho+(1-a)*C*majorityPolynomial rho)
    (hpure : C*(c-rho)*(3*rho-2*rho^2) ≤ K)
    (hmixed : (c-rho)*(a0+(1-a0)*C*(3*rho-2*rho^2)) ≤ K) :
    (c-rho)*p ≤ K*rho := by
  have hcr : 0 ≤ c-rho := by linarith only [hr1,hc]
  have hscale := mul_le_mul_of_nonneg_left hp hcr
  have hpoly : majorityPolynomial rho=rho*(3*rho-2*rho^2) := by
    unfold majorityPolynomial
    ring
  by_cases hs : 0 ≤ rho-C*majorityPolynomial rho
  · have hdiff := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haa hs) hcr
    have hK := mul_le_mul_of_nonneg_right hmixed hr0
    rw [hpoly] at hscale hdiff
    nlinarith only [hscale,hdiff,hK]
  · have hdiff := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hs)
    have hmul := mul_nonpos_of_nonneg_of_nonpos hcr hdiff
    have hK := mul_le_mul_of_nonneg_right hpure hr0
    rw [hpoly] at hscale hmul
    nlinarith only [hscale,hmul,hK]

/-- Per-vertex charge using an actual degree and crossing degree. The
zero-vote probability is paid only on the original minority side. -/
theorem majority_joint_vertex_bound {d b z dm tau C a a0 K p zero : ℝ}
    (hz : 0<z) (hdm : 0<dm) (htau : 0 ≤ tau)
    (hd : dm*z ≤ d) (hb0 : 0 ≤ b) (hbd : b ≤ d)
    (ha : 0 ≤ a) (haa : a ≤ a0) (hzero : 0 ≤ zero) (hK : 0 ≤ K)
    (hp : p ≤ a*(b/d)+(1-a)*C*majorityPolynomial (b/d)+zero)
    (hpure : C*(1+tau/dm-b/d)*(3*(b/d)-2*(b/d)^2) ≤ K)
    (hmixed : (1+tau/dm-b/d)*(a0+(1-a0)*C*(3*(b/d)-2*(b/d)^2)) ≤ K) :
    (d-b+tau*z)*p ≤ K*b+(d+tau*z)*zero := by
  have hdpos : 0<d := (mul_pos hdm hz).trans_le hd
  have hr0 : 0 ≤ b/d := div_nonneg hb0 hdpos.le
  have hr1 : b/d ≤ 1 := (div_le_one hdpos).mpr hbd
  have hc : 1 ≤ 1+tau/dm := by linarith [div_nonneg htau hdm.le]
  have hmix := majority_joint_mixture_bound hr0 hr1 hc ha haa
    (show p-zero ≤ a*(b/d)+(1-a)*C*majorityPolynomial (b/d) by linarith only [hp])
    hpure hmixed
  have hcost : 0 ≤ d-b+tau*z := add_nonneg (sub_nonneg.mpr hbd) (mul_nonneg htau hz.le)
  have hcoef : d-b+tau*z ≤ d*(1+tau/dm-b/d) := by
    have hh := mul_le_mul_of_nonneg_right hd htau
    have hupper : tau*z ≤ d*tau/dm := (le_div_iff₀ hdm).mpr (by nlinarith only [hh])
    calc
      _ ≤ d-b+d*tau/dm := by linarith only [hupper]
      _ = _ := by field_simp; ring
  by_cases hnonneg : 0 ≤ p-zero
  · have hmul := mul_le_mul_of_nonneg_right hcoef hnonneg
    have hm := mul_le_mul_of_nonneg_left hmix hdpos.le
    have hcancel : d*(K*(b/d))=K*b := by field_simp
    rw [hcancel] at hm
    have hbzero := mul_nonneg hb0 hzero
    nlinarith only [hm,hmul,hbzero]
  · have hh := mul_nonpos_of_nonneg_of_nonpos hcost (le_of_not_ge hnonneg)
    have hKb : 0 ≤ K*b := mul_nonneg hK hb0
    have hbzero := mul_nonneg hb0 hzero
    nlinarith only [hh,hKb,hbzero]

end
end Cycle12
