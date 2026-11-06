import Cycle12.RoutingScaleEndpoint12

namespace Cycle12.Global12
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem balanced_capacity_point :
    (((9108255590499204388240354266654047353/1000000000000000000000000):ℚ):ℝ) ≤ (2:ℝ)^(((430503119147487050804007/10000000000000000000000):ℚ):ℝ) ∧
    (2:ℝ)^(((430503119147487050804007/10000000000000000000000):ℚ):ℝ) ≤ (((9108255590499204388240354724907826133/1000000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y := (503119147487050804007/10000000000000000000000)) (43)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem balanced_capacity_base : 2112/(p^2*comparison_bank^2) ≤ (2:ℝ)^((2*s-rho)*w0) := by
  have he : (2*s-rho)*w0 = (((430503119147487050804007/10000000000000000000000):ℚ):ℝ) := by norm_num [s,rho,w0]
  rw [he]
  exact (show 2112/(p^2*comparison_bank^2) ≤ (((9108255590499204388240354266654047353/1000000000000000000000000):ℚ):ℝ) by norm_num [p,comparison_bank]).trans balanced_capacity_point.1

theorem completion_capacity_point :
    (((150305890196036919913995490896942546624410413/1000000000000000000000000):ℚ):ℝ) ≤ (2:ℝ)^(((39136647195226095527637/583898436288774103240):ℚ):ℝ) ∧
    (2:ℝ)^(((39136647195226095527637/583898436288774103240):ℚ):ℝ) ≤ (((939411813725230749462471842965963337090507/6250000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y := (15451963878230610557/583898436288774103240)) (67)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem completion_capacity_base : 2112/(p^2*completion_bank^2) ≤ (2:ℝ)^((2*s-rho)*wA) := by
  have he : (2*s-rho)*wA = (((39136647195226095527637/583898436288774103240):ℚ):ℝ) := by norm_num [s,rho,wA]
  rw [he]
  exact (show 2112/(p^2*completion_bank^2) ≤ (((150305890196036919913995490896942546624410413/1000000000000000000000000):ℚ):ℝ) by norm_num [p,completion_bank]).trans completion_capacity_point.1

end
end Cycle12.Global12
