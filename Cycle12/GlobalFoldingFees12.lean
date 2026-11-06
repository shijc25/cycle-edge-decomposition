import Cycle12.GlobalPotential12

namespace Cycle12.Global12
open Real Set
noncomputable section

def batchFee (w : ℝ) : ℝ :=
  ((2:ℝ)^(growth*wA)/(4*c))*(2:ℝ)^(-(alpha+s-rho+growth)*w)+
    (1/2:ℝ)*(2:ℝ)^(-(lam+s-rho)*w)
def hubFee (w : ℝ) : ℝ :=
  ((2:ℝ)^(growth*wA)/(2*c))*(2:ℝ)^(-growth*w)+(1/2048:ℝ)

theorem batchFee_identity (w : ℝ) :
    batchFee w=(2:ℝ)^((rho-s-alpha)*w)/(4*c*teamGrowth w)+(2:ℝ)^((rho-s-lam)*w)/2 := by
  have he : (2:ℝ)^(growth*wA)*(2:ℝ)^(-(alpha+s-rho+growth)*w)=
      (2:ℝ)^((rho-s-alpha)*w)/teamGrowth w := by
    rw [←rpow_add (by norm_num : (0:ℝ)<2),teamGrowth,two_power_ratio]
    congr 1
    ring
  have hl : -(lam+s-rho)*w=(rho-s-lam)*w := by ring
  unfold batchFee
  calc
    _ = ((2:ℝ)^(growth*wA)*(2:ℝ)^(-(alpha+s-rho+growth)*w))/(4*c)+
      (2:ℝ)^((rho-s-lam)*w)/2 := by rw [hl]; ring
    _ = _ := by rw [he]; ring

theorem hubFee_identity (w : ℝ) : hubFee w=1/(2*c*teamGrowth w)+(1/2048:ℝ) := by
  have he : (2:ℝ)^(growth*wA)*(2:ℝ)^(-growth*w)=1/teamGrowth w := by
    rw [←rpow_add (by norm_num : (0:ℝ)<2),teamGrowth]
    rw [show growth*wA+-growth*w=-(growth*(w-wA)) by ring,rpow_neg (by norm_num)]
    simp only [one_div]
  unfold hubFee
  calc
    _ = ((2:ℝ)^(growth*wA)*(2:ℝ)^(-growth*w))/(2*c)+(1/2048:ℝ) := by ring
    _ = _ := by rw [he]; ring

theorem batchFee_nonneg (w : ℝ) : 0 ≤ batchFee w := by unfold batchFee c; positivity
theorem hubFee_nonneg (w : ℝ) : 0 ≤ hubFee w := by unfold hubFee c; positivity

theorem batchFee_antitone : Antitone batchFee := by
  intro x y hxy
  unfold batchFee
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by unfold c; positivity)
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hxy
      (show 0≤alpha+s-rho+growth by norm_num [alpha,s,rho,growth])
    linarith only [hh]
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply rpow_le_rpow_of_exponent_le (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hxy (show 0≤lam+s-rho by norm_num [lam,s,rho])
    linarith only [hh]

theorem hubFee_antitone : Antitone hubFee := by
  intro x y hxy
  unfold hubFee
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by unfold c; positivity)
  apply rpow_le_rpow_of_exponent_le (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hxy (show 0≤growth by norm_num [growth,s,rho,alpha])
  linarith only [hh]

def foldMassCoefficient (P w : ℝ) : ℝ :=
  (1+C*eta)*P+sigma+batchFee w+hubFee w-C*kappa*globalPhi (b*w)

theorem foldMassCoefficient_antitone (P : ℝ) : Antitone (foldMassCoefficient P) := by
  intro x y hxy
  have hb := batchFee_antitone hxy
  have hh := hubFee_antitone hxy
  have hp := mul_le_mul_of_nonneg_left
    (globalPhi_monotone (mul_le_mul_of_nonneg_left hxy (show 0 ≤ b by norm_num [b])))
    (show 0≤C*kappa by norm_num [C,kappa])
  unfold foldMassCoefficient
  linarith only [hb,hh,hp]

/-- Once an actual fold packing has this ledger, the renewal identity
pays its positive error and the certified mass coefficient closes it. -/
theorem folding_potential_payment {w n S P cost : ℝ} (hw : wA≤w) (hn : 0≤n) (hS : 0≤S)
    (hx : w≤logb 2 n) (hcoef : foldMassCoefficient P w≤0)
    (hcost : cost≤C*globalPhi (b*w)*n+foldMassCoefficient P w*S+C*lossH w*n) :
    cost≤C*globalPhi (logb 2 n)*n := by
  have hphi := globalPhi_fold_budget hw hx
  have hpay := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hphi (show 0≤C by norm_num [C])) hn
  have hnegative := mul_nonpos_of_nonpos_of_nonneg hcoef hS
  nlinarith only [hcost,hpay,hnegative]

end
end Cycle12.Global12
