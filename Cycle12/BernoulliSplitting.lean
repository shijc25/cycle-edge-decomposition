import Cycle12.BernoulliSmallTailOrder

namespace Cycle12
open Polynomial Finset
noncomputable section

def smallTailTwo (P : Polynomial ℝ) : ℝ := P.coeff 0+P.coeff 1+P.coeff 2

/-- Splitting one Bernoulli parameter in half preserves its mean.
The exact change in the lower CDF involves only the first two masses
of the remaining distribution. -/
theorem bernoulli_split_cdf_identity (p : ℝ) (Q : Polynomial ℝ) :
    smallTailTwo ((realBernoulliPolynomial (p/2)*realBernoulliPolynomial (p/2))*Q)-
      smallTailTwo (realBernoulliPolynomial p*Q)=p^2/4*(Q.coeff 2-Q.coeff 1) := by
  simp only [smallTailTwo,mul_assoc,bernoulli_step_coeff_zero,
    bernoulli_step_coeff_succ _ _ 0,bernoulli_step_coeff_succ _ _ 1]
  ring

theorem bernoulli_split_cdf_le {I : Type} [DecidableEq I] (S : Finset I)
    (q : I → ℝ) (hq : ∀ i∈S, 0 ≤ q i ∧ q i ≤ 1) {p : ℝ}
    (hp : p ≤ 1) (hmean : 3 ≤ p+∑ i∈S, q i) :
    smallTailTwo (realBernoulliPolynomial p*bernoulliPGF S q) ≤
      smallTailTwo ((realBernoulliPolynomial (p/2)*realBernoulliPolynomial (p/2))*bernoulliPGF S q) := by
  have hmode := bernoulli_coeff_two_ge_one S q hq (by linarith only [hp,hmean])
  apply sub_nonneg.mp
  rw [bernoulli_split_cdf_identity]
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (sub_nonneg.mpr hmode)

end
end Cycle12
