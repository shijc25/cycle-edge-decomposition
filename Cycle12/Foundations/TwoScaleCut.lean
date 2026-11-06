import Mathlib

namespace Cycle13

/-- The scalar part of the two-scale branch-cut lemma. Graph cut-size and
degree-counting hypotheses must be established when this lemma is applied. -/
theorem two_scale_branch_cut {u b t δ c h₀ h₁ L cut : ℝ}
    (hb : 0 ≤ b) (hbt : b ≤ t) (hc : 0 ≤ c)
    (hh₀ : 0 < h₀) (hh₁ : 0 < h₁)
    (hdegree : b * (δ - u) ≤ cut)
    (hglobal : h₀ * u ≤ cut)
    (hlocal : u ≤ L → h₁ * u ≤ cut)
    (hsmallBudget : c * (t + h₁) ≤ h₁ * δ)
    (hlargeBudget : t * c ≤ h₀ * L) :
    c * b ≤ cut := by
  by_cases hu : u ≤ δ - c
  · have hm := mul_le_mul_of_nonneg_left (show c ≤ δ - u by linarith) hb
    nlinarith
  · have hcb : c * b ≤ t * c := by nlinarith [mul_le_mul_of_nonneg_left hbt hc]
    by_cases hL : u ≤ L
    · have hh := hlocal hL
      have hm := mul_le_mul_of_nonneg_left (show δ - c ≤ u by linarith) hh₁.le
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left (show L ≤ u by linarith) hh₀.le
      linarith

end Cycle13
