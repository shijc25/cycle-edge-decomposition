import Mathlib

namespace Cycle12.Global12
noncomputable section
def w0 : ℝ := (10170985991133/100000000000)
def s : ℝ := (38082365177/50000000000)
def theta0 : ℝ := (2048519349/2500000000)
def theta2 : ℝ := (15961744051/20000000000)
def alpha : ℝ := (13908880001/25000000000)
def lam : ℝ := (3511913879/10000000000)
def b : ℝ := (3004140221/4000000000)
def gamma : ℝ := (2460109537/1562500000)
def delta : ℝ := (3454748071/50000000000)
def eps : ℝ := (3093377987/100000000000)
def c : ℝ := (284161497/500000000)
def prune_a : ℝ := (36700631257/50000000000)
def theta1 : ℝ := (10059807341/12500000000)
def rho : ℝ := (110002874129/100000000000)
def wA : ℝ := (2311587725257500000000/14597460907219352581)
def eta : ℝ := (244357/2000000000)
def M : ℝ := (10218421973/10000000000)
def overlap : ℝ := (10077234539/5000000000)
def batch : ℝ := (1225527173/10000000000)
def router_length : ℝ := (30589490361/5000000000)
def route_load : ℝ := (7519120361/500000000)
def order_bound : ℝ := (7065355693/10000000000)
def C : ℝ := (485/42)
def sigma : ℝ := (23/42)
def kappa : ℝ := (999999/1000000)
def edge_bias : ℝ := (511/512)
def split_deviation : ℝ := (1/1024)
def p : ℝ := (244357/8000000000)
def router_bank : ℝ := (1044483/1048576)
def completion_bank : ℝ := (1023/1048576)
def router_constant : ℝ := (52902787547485085406377454545012954383041/6250000000000000000000000000000000000)
def phi0 : ℝ := (46220729/50000000)
def q0 : ℝ := theta1*theta2

theorem scale_identities : rho=1+delta+eps ∧ q0*wA=w0 := by
  norm_num [rho,delta,eps,q0,theta1,theta2,wA,w0]

theorem scale_order : 0<s ∧ s<theta2 ∧ theta2≤theta1 ∧ theta1≤theta0 ∧ theta0<1 ∧
    0<w0 ∧ 0<wA ∧ 0<delta ∧ 0<eps ∧ 0<overlap := by
  norm_num [s,theta0,theta1,theta2,w0,wA,delta,eps,overlap]

end
end Cycle12.Global12
