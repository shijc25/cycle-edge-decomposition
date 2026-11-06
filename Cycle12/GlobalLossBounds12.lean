import Cycle12.GlobalLossFunctions12

namespace Cycle12.Global12
open Real
noncomputable section

theorem lossF_upper {w f : ℝ} (hw : wA≤w)
    (hf : (2:ℝ)^(-(alpha-s*q0)*w)≤f) :
    lossF w≤((1001/1000:ℝ)+(rho-s)*q0*w)*f := by
  have hw0 := (show 0≤wA by norm_num [wA]).trans hw
  have hh := mul_nonneg (show 0≤(rho-s)*q0 by norm_num [rho,s,q0,theta1,theta2]) hw0
  exact mul_le_mul_of_nonneg_left hf (by linarith only [hh])

theorem lossH_point_upper {w f o j u v g : ℝ} (hw : wA≤w)
    (hf : lossF w≤f)
    (ho : scaleMassSeries theta2 (delta*theta2^2*w)≤o)
    (hj : scaleMassSeries theta2 (eps*theta2^2*w)≤j)
    (hu : (2:ℝ)^(-(s-lam)*w)≤u) (hv : (2:ℝ)^(-(s+b-lam-rho)*w)≤v)
    (hg : (2:ℝ)^(-growth*(w-wA))≤g) :
    lossH w≤overlap*M*o+kappa*(M^2*f+(M*u+2*M^2*v))+
      (batch*(overlap*M*o)+(M/2)*j+(gamma*M/(2*c))*f*g)/C := by
  have hO : lossO w≤overlap*M*o := mul_le_mul_of_nonneg_left ho (by norm_num [overlap,M])
  have hN : lossN w≤M^2*f := mul_le_mul_of_nonneg_left hf (sq_nonneg _)
  have hJ : lossJ w≤(M/2)*j := mul_le_mul_of_nonneg_left hj (by norm_num [M])
  have hU : lossU w≤M*u+2*M^2*v := add_le_add
    (mul_le_mul_of_nonneg_left hu (by norm_num [M]))
    (mul_le_mul_of_nonneg_left hv (by positivity))
  have hcoef : 0≤gamma*M/(2*c) := by norm_num [gamma,M,c]
  have hV : lossV w≤(gamma*M/(2*c))*f*g := by
    rw [lossV_growth_form]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf hcoef) hg
      (rpow_nonneg (by norm_num) _) (mul_nonneg hcoef ((lossF_nonneg hw).trans hf))
  unfold lossH
  exact add_le_add (add_le_add hO (mul_le_mul_of_nonneg_left (add_le_add hN hU)
    (by norm_num [kappa])))
    (div_le_div_of_nonneg_right (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hO (by norm_num [batch])) hJ) hV) (by norm_num [C]))

end
end Cycle12.Global12
