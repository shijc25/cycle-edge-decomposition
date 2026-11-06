import Cycle12.Foundations.MixedSplitBudget
import Mathlib.Analysis.Convex.Slope

namespace Cycle13.MixedSample
open Real Set Finset
noncomputable section

theorem cutShapeS_zero : cutShapeS 0=1 := by norm_num [cutShapeS]
theorem cutShapeU_zero : cutShapeU 0=1 := by simp [cutShapeU,cutShapeS_zero]

theorem cutShapeS_symm (y : ℝ) : cutShapeS (1-y)=cutShapeS y := by
  simp only [cutShapeS,sub_sub_cancel]
  ring

theorem cutShapeU_symm (y : ℝ) : cutShapeU (1-y)=cutShapeU y := by
  rw [cutShapeU,cutShapeS_symm,cutShapeU]

theorem cutShapeS_as_rpow {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    cutShapeS y=y^(3/2:ℝ)+(1-y)^(3/2:ℝ) := by
  rw [rpow_three_halves hy.1,rpow_three_halves (sub_nonneg.mpr hy.2)]
  rfl

theorem cutShapeS_convex : ConvexOn ℝ (Icc (0:ℝ) 1) cutShapeS := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hc := convexOn_rpow (by norm_num : (1:ℝ) ≤ 3/2)
  have h₁ := hc.2 hx.1 hy.1 ha hb hab
  have h₂ := hc.2 (show 0 ≤ 1-x by linarith [hx.2])
    (show 0 ≤ 1-y by linarith [hy.2]) ha hb hab
  have hxy : a*x+b*y ∈ Icc (0:ℝ) 1 := (convex_Icc (0:ℝ) 1) hx hy ha hb hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  rw [cutShapeS_as_rpow hxy,cutShapeS_as_rpow hx,cutShapeS_as_rpow hy]
  have he : a*(1-x)+b*(1-y)=1-(a*x+b*y) := by nlinarith only [hab]
  rw [he] at h₂
  linarith only [h₁,h₂]

private theorem scaled_cut_norm {a x : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (0:ℝ) 1) :
    ((a*x)^(3/2:ℝ)+(a*(1-x))^(3/2:ℝ))^(2/3:ℝ)=a*cutShapeU x := by
  rw [mul_rpow ha hx.1,mul_rpow ha (sub_nonneg.mpr hx.2),← mul_add,
    mul_rpow (rpow_nonneg ha _) (by positivity [hx.1,sub_nonneg.mpr hx.2]),
    ← rpow_mul ha,show (3/2:ℝ)*(2/3)=1 by norm_num,rpow_one]
  rw [cutShapeU,cutShapeS_as_rpow hx]

/-- Convexity of the two-coordinate L^(3/2) norm, including both endpoints.
It supplies the sharper cube-root secants needed by the sparse-cut profile. -/
theorem cutShapeU_convex : ConvexOn ℝ (Icc (0:ℝ) 1) cutShapeU := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := Real.Lp_add_le_of_nonneg (s:=(univ : Finset (Fin 2)))
    (f:=![a*x,a*(1-x)]) (g:=![b*y,b*(1-y)]) (by norm_num : (1:ℝ) ≤ 3/2)
    (by intro i _; fin_cases i; exact mul_nonneg ha hx.1; exact mul_nonneg ha (sub_nonneg.mpr hx.2))
    (by intro i _; fin_cases i; exact mul_nonneg hb hy.1; exact mul_nonneg hb (sub_nonneg.mpr hy.2))
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [show (1:ℝ)/(3/2)=2/3 by norm_num,scaled_cut_norm ha hx,scaled_cut_norm hb hy] at hh
  have he : a*(1-x)+b*(1-y)=1-(a*x+b*y) := by nlinarith only [hab]
  rw [he] at hh
  have hxy : a*x+b*y ∈ Icc (0:ℝ) 1 := (convex_Icc (0:ℝ) 1) hx hy ha hb hab
  simpa only [smul_eq_mul,cutShapeU,cutShapeS_as_rpow hxy] using hh

theorem cutShapeS_secant {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (1-cutShapeS z)/z ≤ (1-cutShapeS y)/y := by
  have hh := cutShapeS_convex.secant_mono (by simp : (0:ℝ) ∈ Set.Icc 0 1)
    ⟨hy.le,hyz.trans hz⟩ ⟨hy.le.trans hyz,hz⟩ hy.ne' (hy.trans_le hyz).ne' hyz
  simp only [cutShapeS_zero,sub_zero] at hh
  convert neg_le_neg hh using 1 <;> ring

theorem cutShapeU_secant {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (1-cutShapeU z)/z ≤ (1-cutShapeU y)/y := by
  have hh := cutShapeU_convex.secant_mono (by simp : (0:ℝ) ∈ Set.Icc 0 1)
    ⟨hy.le,hyz.trans hz⟩ ⟨hy.le.trans hyz,hz⟩ hy.ne' (hy.trans_le hyz).ne' hyz
  simp only [cutShapeU_zero,sub_zero] at hh
  convert neg_le_neg hh using 1 <;> ring

theorem cutShapeU_midpoint_min {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) :
    cutShapeU (1/2) ≤ cutShapeU y := by
  have hh := cutShapeU_convex.2 hy
    (show 1-y ∈ Icc (0:ℝ) 1 from ⟨by linarith [hy.2],by linarith [hy.1]⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul,cutShapeU_symm] at hh
  convert hh using 1 <;> congr 1 <;> ring

end
end Cycle13.MixedSample
