import Cycle12.FixedUpperCantelli

namespace Cycle12
open Cycle13
noncomputable section

theorem normalized_cantelli_ratio {variance deviation scale v gap : ℝ}
    (hvar : 0 ≤ variance) (hscale : 0 < scale) (hgap : 0 < gap)
    (hv : variance ≤ v*scale^2) (hdev : gap*scale ≤ deviation) :
    variance/(variance+deviation^2) ≤ v/(v+gap^2) := by
  have hs2 : 0 < scale^2 := sq_pos_of_pos hscale
  have hv0 : 0 ≤ v := by nlinarith only [hvar,hv,hs2]
  have hd : 0 < deviation := (mul_pos hgap hscale).trans_le hdev
  have hsq : (gap*scale)^2 ≤ deviation^2 := pow_le_pow_left₀ (mul_pos hgap hscale).le hdev 2
  have h₁ := mul_le_mul_of_nonneg_right hv (sq_nonneg gap)
  have h₂ := mul_le_mul_of_nonneg_left hsq hv0
  apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos hvar (sq_pos_of_pos hd))
    (add_pos_of_nonneg_of_pos hv0 (sq_pos_of_pos hgap))).mpr
  nlinarith only [h₁,h₂]

theorem normalized_cantelli_lower {Ω : Type*} [Fintype Ω] (mu : FiniteLaw Ω)
    (X : Ω → ℝ) {m variance scale v gap threshold : ℝ}
    (hmean : mu.expect X=m) (hvariance : mu.expect (fun x => (X x-m)^2) ≤ variance)
    (hscale : 0 < scale) (hgap : 0 < gap)
    (hv : variance ≤ v*scale^2) (hdev : gap*scale ≤ m-threshold) :
    mu.prob (fun x => X x ≤ threshold) ≤ v/(v+gap^2) := by
  have hvar := (mu.expect_nonneg (fun x => sq_nonneg (X x-m))).trans hvariance
  have hd : 0 < m-threshold := (mul_pos hgap hscale).trans_le hdev
  have hh := mu.cantelli_lower X hmean hvariance hd
  simp only [sub_sub_cancel] at hh
  exact hh.trans (normalized_cantelli_ratio hvar hscale hgap hv hdev)

theorem normalized_cantelli_upper {Ω : Type*} [Fintype Ω] (mu : FiniteLaw Ω)
    (X : Ω → ℝ) {m variance scale v gap threshold : ℝ}
    (hmean : mu.expect X=m) (hvariance : mu.expect (fun x => (X x-m)^2) ≤ variance)
    (hscale : 0 < scale) (hgap : 0 < gap)
    (hv : variance ≤ v*scale^2) (hdev : gap*scale ≤ threshold-m) :
    mu.prob (fun x => threshold ≤ X x) ≤ v/(v+gap^2) := by
  have hvar := (mu.expect_nonneg (fun x => sq_nonneg (X x-m))).trans hvariance
  have hd : 0 < threshold-m := (mul_pos hgap hscale).trans_le hdev
  have hh := finite_law_cantelli_upper mu X hmean hvariance hd
  simp only [add_sub_cancel] at hh
  exact hh.trans (normalized_cantelli_ratio hvar hscale hgap hv hdev)

end
end Cycle12
