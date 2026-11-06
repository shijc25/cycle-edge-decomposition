import Cycle12.EntropyScaleSplit

namespace Cycle12
open Real SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section

theorem two_power_ratio (a b : ℝ) : (2:ℝ)^a/(2:ℝ)^b=(2:ℝ)^(a-b) :=
  (Real.rpow_sub (by norm_num) a b).symm

theorem entropy_power_rate (s rho w : ℝ) :
    log ((2:ℝ)^(rho*w)/(2:ℝ)^(s*w))/log 2=(rho-s)*w := by
  rw [two_power_ratio,Real.log_rpow (by norm_num)]
  have hl : log (2:ℝ)≠0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  <;> ring

theorem power_cycle_charge (eps w : ℝ) :
    (2:ℝ)^w/(2*(2:ℝ)^((1+eps)*w))=(2:ℝ)^(-eps*w)/2 := by
  rw [show (2:ℝ)^w/(2*(2:ℝ)^((1+eps)*w)) =
    ((2:ℝ)^w/(2:ℝ)^((1+eps)*w))/2 by ring,two_power_ratio]
  congr 2
  ring

theorem power_overlap_identity (eps rho w : ℝ) :
    2*(2:ℝ)^((1+eps)*w)/((2:ℝ)^(rho*w)-(2:ℝ)^((1+eps)*w)-2) =
      2*(2:ℝ)^(-(rho-1-eps)*w)/
        (1-(2:ℝ)^(-(rho-1-eps)*w)-2*(2:ℝ)^(-rho*w)) := by
  have hx : (2:ℝ)^(-(rho-1-eps)*w)=(2:ℝ)^((1+eps)*w)/(2:ℝ)^(rho*w) := by
    rw [two_power_ratio]
    congr 1
    ring
  have hy : (2:ℝ)^(-rho*w)=1/(2:ℝ)^(rho*w) := by
    rw [show -rho*w=-(rho*w) by ring,Real.rpow_neg (by norm_num)]
    simp only [one_div]
  rw [hx,hy]
  have hp : (2:ℝ)^(rho*w)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp

theorem power_overlap_bound {eps rho w0 w chi : ℝ}
    (hdelta : 0≤rho-1-eps) (hrho : 0≤rho) (hw : w0≤w) (hchi : 0≤chi)
    (hbase : 0<1-(2:ℝ)^(-(rho-1-eps)*w0)-2*(2:ℝ)^(-rho*w0))
    (hcoef : 2≤chi*(1-(2:ℝ)^(-(rho-1-eps)*w0)-2*(2:ℝ)^(-rho*w0))) :
    (2:ℝ)^((1+eps)*w)+2<(2:ℝ)^(rho*w) ∧
    2*(2:ℝ)^((1+eps)*w)/((2:ℝ)^(rho*w)-(2:ℝ)^((1+eps)*w)-2) ≤
      chi*(2:ℝ)^(-(rho-1-eps)*w) := by
  have hx : (2:ℝ)^(-(rho-1-eps)*w)≤(2:ℝ)^(-(rho-1-eps)*w0) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hdelta (sub_nonneg.mpr hw)]
  have hy : (2:ℝ)^(-rho*w)≤(2:ℝ)^(-rho*w0) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [mul_nonneg hrho (sub_nonneg.mpr hw)]
  have hden : 0<1-(2:ℝ)^(-(rho-1-eps)*w)-2*(2:ℝ)^(-rho*w) := by
    linarith only [hbase,hx,hy]
  have hcoef' : 2≤chi*(1-(2:ℝ)^(-(rho-1-eps)*w)-2*(2:ℝ)^(-rho*w)) :=
    hcoef.trans (mul_le_mul_of_nonneg_left (by linarith only [hx,hy]) hchi)
  constructor
  · have hxid : (2:ℝ)^(-(rho-1-eps)*w)=(2:ℝ)^((1+eps)*w)/(2:ℝ)^(rho*w) := by
      rw [two_power_ratio]
      congr 1
      ring
    have hyid : (2:ℝ)^(-rho*w)=1/(2:ℝ)^(rho*w) := by
      rw [show -rho*w=-(rho*w) by ring,Real.rpow_neg (by norm_num)]
      simp only [one_div]
    rw [hxid,hyid] at hden
    have hmul := mul_pos hden (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (rho*w))
    have hp : (2:ℝ)^(rho*w)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp at hmul
    rw [mul_comm w rho] at hmul
    linarith only [hmul]
  · rw [power_overlap_identity]
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_right hcoef'
      (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (-(rho-1-eps)*w))
    nlinarith only [hh]

end
end Cycle12
