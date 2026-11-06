import Cycle12.GlobalFoldingFees12
import Cycle12.Foundations.ScaleSeriesCertificates

namespace Cycle12.Global12
open Real
noncomputable section
set_option maxHeartbeats 600000

theorem batchAnchorTerm0 : (2:ℝ)^((((-20154618933510405361587/583898436288774103240):ℚ):ℝ)) ≤ (((40667387876477/1000000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(281826336596688251813/583898436288774103240)) (-35)
    (q:=(-20154618933510405361587/583898436288774103240)) (L:=(10166846969119/250000000000000000000000)) (U:=(40667387876477/1000000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem batchAnchorTerm1 : (2:ℝ)^((((-236890588223203767309/116779687257754820648):ℚ):ℝ)) ≤ (((122552716957080796659679/500000000000000000000000):ℚ):ℝ) := by
  exact (Cycle13.certified_power_two (y:=(113448473550060694635/116779687257754820648)) (-3)
    (q:=(-236890588223203767309/116779687257754820648)) (L:=(61276358478540398220013/250000000000000000000000)) (U:=(122552716957080796659679/500000000000000000000000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2

theorem batchFee_active_cap : batchFee wA ≤ batch := by
  have h0 : (2:ℝ)^((rho-s-alpha)*wA) ≤ (((40667387876477/1000000000000000000000000):ℚ):ℝ) := by
    have he : (rho-s-alpha)*wA=(((-20154618933510405361587/583898436288774103240):ℚ):ℝ) := by norm_num [rho,s,alpha,wA]
    rw [he]
    exact batchAnchorTerm0
  have h1 : (2:ℝ)^((rho-s-lam)*wA) ≤ (((122552716957080796659679/500000000000000000000000):ℚ):ℝ) := by
    have he : (rho-s-lam)*wA=(((-236890588223203767309/116779687257754820648):ℚ):ℝ) := by norm_num [rho,s,lam,wA]
    rw [he]
    exact batchAnchorTerm1
  rw [batchFee_identity]
  simp only [teamGrowth,sub_self,mul_zero,rpow_zero,mul_one]
  exact (add_le_add (div_le_div_of_nonneg_right h0 (by norm_num [c]))
    (div_le_div_of_nonneg_right h1 (by norm_num))).trans (by norm_num [c,batch])

theorem batchFee_uniform_cap {w : ℝ} (hw : wA ≤ w) : batchFee w ≤ batch :=
  (batchFee_antitone hw).trans batchFee_active_cap

def groupFee (w : ℝ) : ℝ := hubFee w-(1/2048:ℝ)

theorem groupFee_identity (w : ℝ) : groupFee w=1/(2*c*teamGrowth w) := by
  rw [groupFee,hubFee_identity]
  ring

theorem groupFee_nonneg (w : ℝ) : 0 ≤ groupFee w := by
  rw [groupFee_identity]
  unfold teamGrowth c
  positivity

theorem groupFee_upper {w : ℝ} (hw : wA ≤ w) : groupFee w ≤ 1/(2*c) := by
  have hh := hubFee_antitone hw
  rw [hubFee_identity wA] at hh
  simp only [teamGrowth,sub_self,mul_zero,rpow_zero,mul_one] at hh
  unfold groupFee
  linarith only [hh]

theorem fold_saving_coefficient_nonneg {w : ℝ} (hw : wA ≤ w) :
    0 ≤ C*kappa*globalPhi (b*w)-groupFee w := by
  have hp := mul_le_mul_of_nonneg_left (globalPhi_lower (b*w))
    (show 0 ≤ C*kappa by norm_num [C,kappa])
  have hg := groupFee_upper hw
  have hh : 1/(2*c) ≤ C*kappa*phi0 := by norm_num [c,C,kappa,phi0]
  linarith only [hp,hg,hh]

/-- Pay the physical fold ledger with the current renewal loss. The
active mass is used with its negative net coefficient before inserting
the deficit; no extra overlap charge for group-size fees is introduced. -/
theorem physical_fold_ledger_payment {w n S A D T P cost : ℝ} (hw : wA ≤ w)
    (hn : 0 ≤ n)
    (hAlo : S-(lossN w+lossU w)*n ≤ A)
    (hAhi : A ≤ S+lossO w*n)
    (hD : D ≤ (1+lossO w)*n) (hT : T ≤ P*S)
    (hcost : cost ≤ (1+C*eta)*T+sigma*S+(1/2048:ℝ)*S+
      (batchFee w+groupFee w)*A+C*globalPhi (b*w)*(D-kappa*A)+(lossJ w+lossV w)*n) :
    cost ≤ C*globalPhi (b*w)*n+foldMassCoefficient P w*S+C*lossH w*n := by
  have hphi := globalPhi_bounds (b*w)
  have hscale0 : 0 ≤ C*globalPhi (b*w) := mul_nonneg (by norm_num [C]) hphi.1.le
  have hscale1 : C*globalPhi (b*w) ≤ C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hphi.2 (show 0 ≤ C by norm_num [C])
  have hcore := mul_le_mul_of_nonneg_left hT (show 0 ≤ 1+C*eta by norm_num [C,eta])
  have hmass := mul_le_mul_of_nonneg_left hD hscale0
  have hsaving := mul_le_mul_of_nonneg_left hAlo (fold_saving_coefficient_nonneg hw)
  have hbatch := mul_le_mul_of_nonneg_left hAhi (batchFee_nonneg w)
  have hN : 0 ≤ lossN w+lossU w := add_nonneg (losses_nonneg hw).2.1 (losses_nonneg hw).2.2.2.1
  have hO : 0 ≤ lossO w := (losses_nonneg hw).1
  have hOerror := mul_le_mul_of_nonneg_right hscale1 (mul_nonneg hO hn)
  have hsavemax : C*kappa*globalPhi (b*w)-groupFee w ≤ C*kappa := by
    have hh := mul_le_mul_of_nonneg_left hphi.2 (show 0 ≤ C*kappa by norm_num [C,kappa])
    have hg := groupFee_nonneg w
    nlinarith only [hh,hg]
  have hNerror := mul_le_mul_of_nonneg_right hsavemax (mul_nonneg hN hn)
  have hBerror := mul_le_mul_of_nonneg_right (batchFee_uniform_cap hw) (mul_nonneg hO hn)
  have hgid : groupFee w+(1/2048:ℝ)=hubFee w := by unfold groupFee; ring
  have hformula : C*globalPhi (b*w)*n+foldMassCoefficient P w*S+C*lossH w*n=
      C*globalPhi (b*w)*n+((1+C*eta)*P+sigma+batchFee w+groupFee w+(1/2048:ℝ)-
        C*kappa*globalPhi (b*w))*S+
      (C*lossO w+C*kappa*(lossN w+lossU w)+batch*lossO w+lossJ w+lossV w)*n := by
    unfold foldMassCoefficient lossH
    have hc : C ≠ 0 := by norm_num [C]
    rw [←hgid]
    field_simp
    <;> ring
  rw [hformula]
  nlinarith only [hcost,hcore,hmass,hsaving,hbatch,hOerror,hNerror,hBerror]

end
end Cycle12.Global12
