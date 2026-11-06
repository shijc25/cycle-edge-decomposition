import Cycle12.CoverGraphCoordinates
import Cycle12.Foundations.MixedCycleBudget

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

/-- The concave cycle allowance at average-degree threshold 4(43/10)^3. -/
def coverCycleBudget (n m : ℝ) : ℝ := cycleBudget n ((216/(43/10)^3)*m)

theorem cover_cycle_budget_eq (n m : ℝ) :
    coverCycleBudget n m=n*cycleFactor (m/(2*(43/10)^3*n)) := by
  unfold coverCycleBudget cycleBudget
  congr 1
  ring

theorem cover_cycle_budget_nonneg {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) :
    0 ≤ coverCycleBudget n m :=
  cycleBudget_nonneg hn (by positivity)

theorem cover_cycle_budget_zero (n : ℝ) : coverCycleBudget n 0=0 := by
  simp [coverCycleBudget,cycleBudget_zero]

theorem cover_cycle_budget_superadditive {n₁ n₂ m₁ m₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    coverCycleBudget n₁ m₁+coverCycleBudget n₂ m₂ ≤ coverCycleBudget (n₁+n₂) (m₁+m₂) := by
  simpa only [coverCycleBudget,mul_add] using
    (cycleBudget_superadditive (m₁:=(216/(43/10)^3)*m₁) (m₂:=(216/(43/10)^3)*m₂) hn₁ hn₂)

theorem cover_cycle_budget_mono_edges {n m₁ m₂ : ℝ} (hn : 0 ≤ n) (hm₁ : 0 ≤ m₁)
    (hmm : m₁ ≤ m₂) : coverCycleBudget n m₁ ≤ coverCycleBudget n m₂ :=
  cycleBudget_mono_edges hn (by positivity) (mul_le_mul_of_nonneg_left hmm (by norm_num))

theorem cover_cycle_budget_mono_order {n₁ n₂ m : ℝ} (hn₁ : 0 < n₁) (hn : n₁ ≤ n₂) :
    coverCycleBudget n₁ m ≤ coverCycleBudget n₂ m := cycleBudget_mono_order hn₁ hn

theorem cover_cycle_budget_le_half {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) :
    coverCycleBudget n m ≤ n/2 := by
  rw [cover_cycle_budget_eq]
  have hh := mul_le_mul_of_nonneg_left (cycleFactor_le_half
    (show (0:ℝ) ≤ m/(2*(43/10)^3*n) by positivity)) hn
  simpa only [mul_one_div] using hh

end
end Cycle12
