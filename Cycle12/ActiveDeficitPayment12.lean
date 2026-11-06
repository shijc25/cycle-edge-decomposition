import Cycle12.ActualActiveBatches12

namespace Cycle12.Global12
open Real Finset
noncomputable section

def parentDeficitFee (w : ℝ) : ℝ := M*lossF w+(2:ℝ)^(-(s-lam)*w)+
  2*M*(2:ℝ)^(-(s+b-lam-rho)*w)

theorem parentDeficitFee_nonneg {w : ℝ} (hw : wA≤w) : 0≤parentDeficitFee w := by
  unfold parentDeficitFee
  have hf := mul_nonneg (show 0≤M by norm_num [M]) (lossF_nonneg hw)
  exact add_nonneg (add_nonneg hf (rpow_nonneg (by norm_num) _))
    (mul_nonneg (by norm_num [M]) (rpow_nonneg (by norm_num) _))

theorem entropy_deficit_ratio (w : ℝ) : entropyRemainder12 (q0*w)/(2:ℝ)^(alpha*w)=lossF w := by
  unfold entropyRemainder12 lossF
  calc
    _ = ((1001/1000:ℝ)+(rho-s)*q0*w)*((2:ℝ)^(s*(q0*w))/(2:ℝ)^(alpha*w)) := by ring
    _ = _ := by rw [two_power_ratio]; congr 2; ring

theorem skipped_deficit_payment {w Y : ℝ} (hY0 : 0≤Y) (hY : Y≤(2:ℝ)^(rho*w)) :
    (2:ℝ)^(lam*w)*(1+2*(M*Y)/(2:ℝ)^(b*w))*(Y/(2:ℝ)^(s*w))≤
      ((2:ℝ)^(-(s-lam)*w)+2*M*(2:ℝ)^(-(s+b-lam-rho)*w))*Y := by
  have hpow (a : ℝ) : 0<(2:ℝ)^(a*w) := rpow_pos_of_pos (by norm_num) _
  have hcount := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hY (show 0≤2*M by norm_num [M])) (hpow b).le
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) hcount) (hpow lam).le)
    (div_nonneg hY0 (hpow s).le)
  have h1 : (2:ℝ)^(lam*w)/(2:ℝ)^(s*w)=(2:ℝ)^(-(s-lam)*w) := by
    rw [two_power_ratio]; congr 1; ring
  have h2 : ((2:ℝ)^(lam*w)*(2:ℝ)^(rho*w))/((2:ℝ)^(b*w)*(2:ℝ)^(s*w))=
      (2:ℝ)^(-(s+b-lam-rho)*w) := by
    rw [←rpow_add (by norm_num : (0:ℝ)<2),←rpow_add (by norm_num : (0:ℝ)<2),two_power_ratio]
    congr 1
    ring
  calc
    _ ≤ (2:ℝ)^(lam*w)*(1+(2*M*(2:ℝ)^(rho*w))/(2:ℝ)^(b*w))*(Y/(2:ℝ)^(s*w)) := by
      convert hh using 1 <;> ring
    _ = ((2:ℝ)^(lam*w)/(2:ℝ)^(s*w)+
      2*M*((2:ℝ)^(lam*w)*(2:ℝ)^(rho*w))/((2:ℝ)^(b*w)*(2:ℝ)^(s*w)))*Y := by ring
    _ = _ := by rw [h1,show 2*M*((2:ℝ)^(lam*w)*(2:ℝ)^(rho*w))/
        ((2:ℝ)^(b*w)*(2:ℝ)^(s*w))=2*M*(((2:ℝ)^(lam*w)*(2:ℝ)^(rho*w))/
        ((2:ℝ)^(b*w)*(2:ℝ)^(s*w))) by ring,h2]

theorem parent_active_deficit_payment {w Y S A : ℝ} (hY0 : 0≤Y) (hY : Y≤(2:ℝ)^(rho*w))
    (hA : S-(entropyRemainder12 (q0*w)*M*Y)/(2:ℝ)^(alpha*w)-
      (2:ℝ)^(lam*w)*(1+2*(M*Y)/(2:ℝ)^(b*w))*(Y/(2:ℝ)^(s*w))≤A) :
    S-parentDeficitFee w*Y≤A := by
  have he : (entropyRemainder12 (q0*w)*M*Y)/(2:ℝ)^(alpha*w)=M*lossF w*Y := by
    rw [←entropy_deficit_ratio]
    ring
  rw [he] at hA
  have hs := skipped_deficit_payment hY0 hY
  unfold parentDeficitFee
  nlinarith only [hA,hs]

theorem parentDeficitFee_identity (w : ℝ) : M*parentDeficitFee w=lossN w+lossU w := by
  unfold parentDeficitFee lossN lossU
  ring

/-- Summing the actual parent deficits produces exactly the N+U term
used in the current renewal loss, including both overlap multipliers. -/
theorem total_active_deficit_payment {I : Type} [Fintype I]
    (Y S A : I → ℝ) {w n : ℝ} (hw : wA≤w)
    (hA : ∀ i,S i-parentDeficitFee w*Y i≤A i) (hY : (∑ i,Y i)≤M*n) :
    (∑ i,S i)-(lossN w+lossU w)*n≤∑ i,A i := by
  have hh := Finset.sum_le_sum (fun i (_ : i∈(univ:Finset I)) => hA i)
  simp only [sum_sub_distrib,←mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left hY (parentDeficitFee_nonneg hw)
  have he := parentDeficitFee_identity w
  have he' : parentDeficitFee w*(M*n)=(lossN w+lossU w)*n := by rw [←he]; ring
  rw [he'] at hm
  linarith only [hh,hm]

end
end Cycle12.Global12
