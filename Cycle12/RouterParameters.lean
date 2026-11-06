import Cycle12.GeneralRouter

namespace Cycle12.Parameters
noncomputable section

def c : ℝ := (284161497/500000000 : ℝ)
def a : ℝ := (36700631257/50000000000 : ℝ)
def R : ℝ := (7519120361/500000000 : ℝ)
def gamma : ℝ := (2460109537/1562500000 : ℝ)
def L : ℝ := (30589490361/5000000000 : ℝ)
def q : ℝ := 1/c

theorem router_parameters_valid :
    0 < q ∧ 0 < a ∧ a < 1 ∧ 1+q+a*q < 2*a^2*(q+2) ∧
    4*(1+q)/a < R ∧ 4/5 ≤ gamma ∧
    0 < 1-a-1/128-1/(R*gamma) ∧ 1/32 < L ∧
    8/(1-a-1/128-1/(R*gamma)) < (L-1/32)^2 := by
  norm_num [q,c,a,R,gamma,L]

theorem all_obstacle_fractions {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ z τ : ℝ, 0 < z ∧ z < 1 ∧ 0 < τ ∧
      1-z-τ=1-a ∧ q*x/z+(1-x)/τ=(1+q)/a ∧
      q*a*x/(2*(1+q)) < z^2/(1+z) := by
  obtain ⟨hq,ha,ha1,hgap,_⟩ := router_parameters_valid
  exact Cycle12.general_router_choice hq ha ha1 hgap hx hx1

end
end Cycle12.Parameters
