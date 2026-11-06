import Cycle12.GlobalParameters12
import Cycle12.Foundations.RationalPowers

namespace Cycle12.Global12
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def growth : ℝ := (3*s-rho-2*alpha)/2

def comparison_bank : ℝ := (511/1024)*(1023/1024)

theorem routing_parameter_identities :
    0 < growth ∧ 0 < s-alpha-growth ∧
    3*s-rho-2*alpha=2*growth ∧
    router_constant=route_load^2*router_length^2 ∧
    0 < comparison_bank ∧ comparison_bank ≤ router_bank ∧ router_bank ≤ 2*comparison_bank := by
  norm_num [growth,s,alpha,rho,router_constant,route_load,router_length,comparison_bank,router_bank]

theorem cubic_scale_point :
    (((1383112867328209082170316963/500000000000000000000000):ℚ):ℝ) ≤ (2:ℝ)^(((1335224281023197354655/116779687257754820648):ℚ):ℝ) ∧
    (2:ℝ)^(((1335224281023197354655/116779687257754820648):ℚ):ℝ) ≤ (((2766225734656418164340642959/1000000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(50647721187894327527/116779687257754820648)) (11)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem cubic_scale_base :
    router_constant*(c+1/17592186044416)^2/router_bank^3 ≤ (2:ℝ)^(2*growth*wA) := by
  have he : 2*growth*wA=(((1335224281023197354655/116779687257754820648):ℚ):ℝ) := by norm_num [growth,s,rho,alpha,wA]
  rw [he]
  exact (show router_constant*(c+1/17592186044416)^2/router_bank^3 ≤ (((1383112867328209082170316963/500000000000000000000000):ℚ):ℝ) by
    norm_num [router_constant,c,router_bank]).trans cubic_scale_point.1

end
end Cycle12.Global12
