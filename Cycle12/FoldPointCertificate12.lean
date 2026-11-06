import Cycle12.GlobalFoldLedger12

namespace Cycle12.Global12
open Real
noncomputable section

/-- Combine the growing team denominator into a single power, so every
folding row can be checked by rational exponential certificates. -/
theorem batchFee_single_power (w : ℝ) : batchFee w=
    (2:ℝ)^((rho-s-alpha)*w-growth*(w-wA))/(4*c)+(2:ℝ)^((rho-s-lam)*w)/2 := by
  rw [batchFee_identity]
  have he : (2:ℝ)^((rho-s-alpha)*w)/(4*c*teamGrowth w)=
      ((2:ℝ)^((rho-s-alpha)*w)/teamGrowth w)/(4*c) := by ring
  rw [he,teamGrowth,two_power_ratio]

theorem groupFee_single_power (w : ℝ) : groupFee w=(2:ℝ)^(-growth*(w-wA))/(2*c) := by
  rw [groupFee_identity,teamGrowth]
  rw [show -growth*(w-wA)=-(growth*(w-wA)) by ring,rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- The exact current folding coefficient is bounded using four explicit
upper certificates; no floating-point decision enters this theorem. -/
theorem folding_point_bound {w p l u v g : ℝ} (hw : wA ≤ w)
    (hl : globalLoss (b*w) ≤ l)
    (hu : (2:ℝ)^((rho-s-alpha)*w-growth*(w-wA)) ≤ u)
    (hv : (2:ℝ)^((rho-s-lam)*w) ≤ v)
    (hg : (2:ℝ)^(-growth*(w-wA)) ≤ g) :
    foldMassCoefficient p w ≤ (1+C*eta)*p+sigma+u/(4*c)+v/2+g/(2*c)+(1/2048:ℝ)-C*kappa*(1-l) := by
  have hB : batchFee w ≤ u/(4*c)+v/2 := by
    rw [batchFee_single_power]
    exact add_le_add (div_le_div_of_nonneg_right hu (by norm_num [c]))
      (div_le_div_of_nonneg_right hv (by norm_num))
  have hG : hubFee w ≤ g/(2*c)+(1/2048:ℝ) := by
    have hh : groupFee w ≤ g/(2*c) := by
      rw [groupFee_single_power]
      exact div_le_div_of_nonneg_right hg (by norm_num [c])
    unfold groupFee at hh
    linarith only [hh]
  have hphi : 1-l ≤ globalPhi (b*w) := by
    rw [globalPhi_large (mul_le_mul_of_nonneg_left hw (by norm_num [b]))]
    linarith only [hl]
  have hpay := mul_le_mul_of_nonneg_left hphi (show 0 ≤ C*kappa by norm_num [C,kappa])
  unfold foldMassCoefficient
  linarith only [hB,hG,hpay]


/-- Fourteen finite rows and the constant threshold after row 16 cover
all subsequent folding scales. -/
theorem folding_rows_to_halfline {lower : ℝ} (hlower : 0 ≤ lower) (p : ℕ → ℝ)
    (hrows : ∀ t,3 ≤ t → t ≤ 16 → foldMassCoefficient (p t) (lower/theta2^(t-3)) ≤ 0)
    (htail : ∀ t,16 ≤ t → p t=p 16) {t : ℕ} (ht : 3 ≤ t) {w : ℝ}
    (hw : lower/theta2^(t-3) ≤ w) : foldMassCoefficient (p t) w ≤ 0 := by
  by_cases hsmall : t ≤ 16
  · exact (foldMassCoefficient_antitone (p t) hw).trans (hrows t ht hsmall)
  · have h16 : 16 ≤ t := by omega
    rw [htail t h16]
    have hp : (theta2⁻¹:ℝ)^13 ≤ (theta2⁻¹:ℝ)^(t-3) :=
      pow_le_pow_right₀ (by norm_num [theta2]) (by omega)
    have hh := mul_le_mul_of_nonneg_left hp hlower
    have hscale : lower/theta2^(16-3) ≤ lower/theta2^(t-3) := by
      simpa only [div_eq_mul_inv,inv_pow] using hh
    exact (foldMassCoefficient_antitone (p 16) (hscale.trans hw)).trans
      (hrows 16 (by omega) le_rfl)

end
end Cycle12.Global12
