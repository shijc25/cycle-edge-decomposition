import Cycle12.Foundations.MixedCutShape
import Mathlib.Analysis.Convex.Jensen

namespace Cycle13.MixedSample
open Real Set
noncomputable section

theorem cutShapeU_antitone {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1/2) :
    cutShapeU z ≤ cutShapeU y := by
  have hh := cutShapeU_convex.le_max_of_mem_Icc
    (show y ∈ Icc (0:ℝ) 1 from ⟨hy,by linarith⟩)
    (show 1-y ∈ Icc (0:ℝ) 1 from ⟨by linarith,by linarith⟩)
    (show z ∈ Icc y (1-y) from ⟨hyz,by linarith⟩)
  simpa only [cutShapeU_symm,max_self] using hh

theorem cutShapeU_cube {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    (cutShapeU y)^3=(cutShapeS y)^2 := by
  unfold cutShapeU
  rw [← rpow_mul_natCast (cutShapeS_nonneg hy hy₁)]
  rw [show (2/3:ℝ)*((3:ℕ):ℝ)=((2:ℕ):ℝ) by norm_num,Real.rpow_natCast]

theorem cutShapeU_half_cube : (cutShapeU (1/2))^3=1/2 := by
  rw [cutShapeU_cube (by norm_num) (by norm_num)]
  have hs : cutShapeS (1/2)=sqrt (1/2) := by norm_num [cutShapeS]; ring
  rw [hs,sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]

theorem cutShapeU_denominator_lower {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    (99/125:ℝ) ≤ cutShapeU y := by
  apply le_trans _ (cutShapeU_midpoint_min ⟨hy,hy₁⟩)
  apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ) ≤ 99/125)
    (cutShapeU_nonneg (by norm_num) (by norm_num)) (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [cutShapeU_half_cube]
  norm_num

/-- A rational enclosure of two square roots and one cube root encloses both
cut-shape functions. Every proposed bound is a checked polynomial inequality. -/
theorem cutShape_bounds_of_roots {y a b c d l u : ℝ}
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (ha₂ : a^2 ≤ y) (hb₂ : y ≤ b^2) (hc₂ : c^2 ≤ 1-y) (hd₂ : 1-y ≤ d^2)
    (hl₃ : l^3 ≤ (y*a+(1-y)*c)^2) (hu₃ : (y*b+(1-y)*d)^2 ≤ u^3) :
    y*a+(1-y)*c ≤ cutShapeS y ∧ cutShapeS y ≤ y*b+(1-y)*d ∧
    l ≤ cutShapeU y ∧ cutShapeU y ≤ u := by
  have hya : a ≤ sqrt y := (sq_le_sq₀ ha (sqrt_nonneg y)).mp (by rwa [sq_sqrt hy])
  have hyb : sqrt y ≤ b := (sq_le_sq₀ (sqrt_nonneg y) hb).mp (by rwa [sq_sqrt hy])
  have hyc : c ≤ sqrt (1-y) := (sq_le_sq₀ hc (sqrt_nonneg (1-y))).mp
    (by rwa [sq_sqrt (sub_nonneg.mpr hy₁)])
  have hyd : sqrt (1-y) ≤ d := (sq_le_sq₀ (sqrt_nonneg (1-y)) hd).mp
    (by rwa [sq_sqrt (sub_nonneg.mpr hy₁)])
  have hlow : y*a+(1-y)*c ≤ cutShapeS y := by
    unfold cutShapeS
    exact add_le_add (mul_le_mul_of_nonneg_left hya hy)
      (mul_le_mul_of_nonneg_left hyc (sub_nonneg.mpr hy₁))
  have hhigh : cutShapeS y ≤ y*b+(1-y)*d := by
    unfold cutShapeS
    exact add_le_add (mul_le_mul_of_nonneg_left hyb hy)
      (mul_le_mul_of_nonneg_left hyd (sub_nonneg.mpr hy₁))
  refine ⟨hlow,hhigh,?_,?_⟩
  · apply (pow_le_pow_iff_left₀ hl (cutShapeU_nonneg hy hy₁) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [cutShapeU_cube hy hy₁]
    exact hl₃.trans (pow_le_pow_left₀ (by positivity : 0 ≤ y*a+(1-y)*c) hlow 2)
  · apply (pow_le_pow_iff_left₀ (cutShapeU_nonneg hy hy₁) hu (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [cutShapeU_cube hy hy₁]
    exact (pow_le_pow_left₀ (cutShapeS_nonneg hy hy₁) hhigh 2).trans hu₃

end
end Cycle13.MixedSample
