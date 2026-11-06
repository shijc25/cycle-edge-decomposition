import Cycle12.PowerDecay12
import Cycle12.GrowingRoutingScales12
import Cycle12.ScaleHalflines12

namespace Cycle12.Global12
open Real Set
noncomputable section

def lossF (w : ℝ) : ℝ :=
  ((1001/1000:ℝ)+(rho-s)*q0*w)*(2:ℝ)^(-(alpha-s*q0)*w)
def lossO (w : ℝ) : ℝ := overlap*M*scaleMassSeries theta2 (delta*theta2^2*w)
def lossN (w : ℝ) : ℝ := M^2*lossF w
def lossJ (w : ℝ) : ℝ := (M/2)*scaleMassSeries theta2 (eps*theta2^2*w)
def lossU (w : ℝ) : ℝ := M*(2:ℝ)^(-(s-lam)*w)+2*M^2*(2:ℝ)^(-(s+b-lam-rho)*w)
def lossV (w : ℝ) : ℝ :=
  (gamma*M*(2:ℝ)^(growth*wA)/(2*c))*lossF w*(2:ℝ)^(-growth*w)
def lossH (w : ℝ) : ℝ := lossO w+kappa*(lossN w+lossU w)+
  (batch*lossO w+lossJ w+lossV w)/C
def lossRate : ℝ := eps*theta2^2

theorem loss_rate_bounds : 0<lossRate ∧ lossRate≤delta*theta2^2 ∧
    lossRate≤alpha-theta0*q0 ∧ lossRate ≤ s-lam ∧ lossRate ≤ s+b-lam-rho ∧
    lossRate≤alpha-theta0*q0+growth := by
  norm_num [lossRate,eps,delta,theta2,alpha,theta0,q0,theta1,s,lam,b,rho,growth]

theorem lossF_nonneg {w : ℝ} (hw : wA≤w) : 0≤lossF w := by
  have hw0 := (show 0≤wA by norm_num [wA]).trans hw
  unfold lossF
  apply mul_nonneg _ (rpow_nonneg (by norm_num) _)
  have hh := mul_nonneg (show 0≤(rho-s)*q0 by norm_num [rho,s,q0,theta1,theta2]) hw0
  linarith only [hh]

theorem lossF_decay : PowerDecay lossF wA (alpha-theta0*q0) := by
  have hs : (rho-s)*q0≤log 2*((theta0-s)*q0)*((1001/1000:ℝ)+(rho-s)*q0*wA) := by
    have hh := mul_le_mul_of_nonneg_right entropy_slope0 (show 0≤q0 by norm_num [q0,theta1,theta2])
    have he : (1001/1000:ℝ)+(rho-s)*q0*wA=(1001/1000:ℝ)+(rho-s)*w0 := by
      norm_num [rho,s,q0,theta1,theta2,wA,w0]
    rw [he]
    nlinarith only [hh]
  have hh := powerDecay_linear_power (r:=alpha-s*q0)
    (show 0≤(1001/1000:ℝ)+(rho-s)*q0*wA by norm_num [rho,s,q0,theta1,theta2,wA])
    (show 0≤(rho-s)*q0 by norm_num [rho,s,q0,theta1,theta2])
    (show 0≤(theta0-s)*q0 by norm_num [theta0,s,q0,theta1,theta2]) hs
  have he : alpha-s*q0-(theta0-s)*q0=alpha-theta0*q0 := by ring
  rw [he] at hh
  exact hh

theorem losses_nonneg {w : ℝ} (hw : wA≤w) :
    0≤lossO w ∧ 0≤lossN w ∧ 0≤lossJ w ∧ 0≤lossU w ∧ 0≤lossV w ∧ 0≤lossH w := by
  have hE (z : ℝ) : 0 ≤ scaleMassSeries theta2 z :=
    tsum_nonneg (fun j => rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
  have hF := lossF_nonneg hw
  have ho : 0≤lossO w := mul_nonneg (by norm_num [overlap,M]) (hE _)
  have hn : 0≤lossN w := mul_nonneg (sq_nonneg _) hF
  have hj : 0≤lossJ w := mul_nonneg (by norm_num [M]) (hE _)
  have hu : 0≤lossU w := by unfold lossU M; positivity
  have hv : 0≤lossV w := by
    unfold lossV
    exact mul_nonneg (mul_nonneg (by unfold gamma M c; positivity) hF) (rpow_nonneg (by norm_num) _)
  refine ⟨ho,hn,hj,hu,hv,?_⟩
  unfold lossH
  exact add_nonneg (add_nonneg ho (mul_nonneg (by norm_num [kappa]) (add_nonneg hn hu)))
    (div_nonneg (add_nonneg (add_nonneg (mul_nonneg (by norm_num [batch]) ho) hj) hv)
      (by norm_num [C]))

/-- This is the original soft routing charge, with the growing team
capacity retained exactly. -/
theorem lossV_identity (w : ℝ) : lossV w=gamma*M*lossF w/(2*c*teamGrowth w) := by
  have hp : (2:ℝ)^(growth*wA)*(2:ℝ)^(-growth*w)=1/teamGrowth w := by
    rw [←rpow_add (by norm_num : (0:ℝ)<2)]
    unfold teamGrowth
    rw [show growth*wA+-growth*w=-(growth*(w-wA)) by ring,rpow_neg (by norm_num)]
    simp only [one_div]
  unfold lossV
  calc
    _ = (gamma*M*lossF w/(2*c))*((2:ℝ)^(growth*wA)*(2:ℝ)^(-growth*w)) := by ring
    _ = _ := by rw [hp]; ring

theorem lossV_growth_form (w : ℝ) :
    lossV w=(gamma*M/(2*c))*lossF w*(2:ℝ)^(-growth*(w-wA)) := by
  unfold lossV
  calc
    _ = (gamma*M/(2*c))*lossF w*((2:ℝ)^(growth*wA)*(2:ℝ)^(-growth*w)) := by ring
    _ = _ := by rw [←rpow_add (by norm_num : (0:ℝ)<2)]; congr 2; ring

theorem lossO_decay : PowerDecay lossO wA (delta*theta2^2) := by
  exact (powerDecay_scale_series (by norm_num [delta,theta2]) (by norm_num [wA])
    (by norm_num [theta2]) (by norm_num [theta2])).mul_const (by norm_num [overlap,M])

theorem lossJ_decay : PowerDecay lossJ wA lossRate := by
  exact (powerDecay_scale_series (by norm_num [eps,theta2]) (by norm_num [wA])
    (by norm_num [theta2]) (by norm_num [theta2])).mul_const (by norm_num [M])

theorem lossN_decay : PowerDecay lossN wA (alpha-theta0*q0) :=
  lossF_decay.mul_const (sq_nonneg _)

theorem lossU_decay : PowerDecay lossU wA lossRate := by
  have h1 := ((powerDecay_power wA (s-lam)).mul_const (show 0≤M by norm_num [M])).weaken
    loss_rate_bounds.2.2.2.1 (fun x _ => mul_nonneg (by norm_num [M]) (rpow_nonneg (by norm_num) _))
  have h2 := ((powerDecay_power wA (s+b-lam-rho)).mul_const
    (show 0≤2*M^2 by positivity)).weaken loss_rate_bounds.2.2.2.2.1
    (fun x _ => mul_nonneg (by positivity) (rpow_nonneg (by norm_num) _))
  exact h1.add h2

theorem lossV_decay : PowerDecay lossV wA (alpha-theta0*q0+growth) := by
  have hc : 0≤gamma*M*(2:ℝ)^(growth*wA)/(2*c) := by
    apply div_nonneg (mul_nonneg (by norm_num [gamma,M]) (rpow_nonneg (by norm_num) _))
      (by norm_num [c])
  exact (lossF_decay.mul_const hc).mul (powerDecay_power wA growth)
    (fun x hx => mul_nonneg hc (lossF_nonneg hx)) (fun x _ => rpow_nonneg (by norm_num) _)

theorem lossH_decay : PowerDecay lossH wA lossRate := by
  have ho := lossO_decay.weaken loss_rate_bounds.2.1 (fun x hx => (losses_nonneg hx).1)
  have hn := lossN_decay.weaken loss_rate_bounds.2.2.1 (fun x hx => (losses_nonneg hx).2.1)
  have hv := lossV_decay.weaken loss_rate_bounds.2.2.2.2.2 (fun x hx => (losses_nonneg hx).2.2.2.2.1)
  have hh := (ho.add ((hn.add lossU_decay).mul_const (show 0≤kappa by norm_num [kappa]))).add
    ((((ho.mul_const (show 0≤batch by norm_num [batch])).add lossJ_decay).add hv).mul_const
      (show 0≤1/C by norm_num [C]))
  convert hh using 1
  funext x
  unfold lossH
  ring

theorem lossH_antitone : AntitoneOn lossH (Ici wA) :=
  lossH_decay.antitone loss_rate_bounds.1.le (fun x hx => (losses_nonneg hx).2.2.2.2.2)

end
end Cycle12.Global12
