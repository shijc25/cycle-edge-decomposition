import Mathlib

namespace Cycle13

/-- This is the numerical transfer only; existence of the weighted decomposition
and the forest bound must still be proved for the actual graph. -/
theorem ordinary_count_of_weighted {cycles singles mass C σ : ℝ}
    (hσ : σ ≤ 1) (hforest : singles ≤ mass)
    (hweighted : cycles + σ * singles ≤ C * mass) :
    cycles + singles ≤ (C + 1 - σ) * mass := by
  have h := mul_le_mul_of_nonneg_left hforest (sub_nonneg.mpr hσ)
  nlinarith

theorem coefficient_identity : (527 : ℚ) / 42 + (1 - 23 / 42) = 13 := by
  norm_num

theorem coefficient13_of_weighted_counts {cycles singles mass : ℝ}
    (hforest : singles ≤ mass)
    (hweighted : cycles + (23 / 42 : ℝ) * singles ≤ (527 / 42 : ℝ) * mass) :
    cycles + singles ≤ 13 * mass := by
  have h := ordinary_count_of_weighted (C := (527 / 42 : ℝ))
    (σ := (23 / 42 : ℝ)) (by norm_num) hforest hweighted
  norm_num at h ⊢
  exact h

end Cycle13
