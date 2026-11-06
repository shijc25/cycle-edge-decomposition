import Cycle12.Foundations.MixedCutBudget

namespace Cycle13.MixedSample
open Real
noncomputable section

def cutShapeS (y : ℝ) : ℝ := y*sqrt y+(1-y)*sqrt (1-y)
def cutShapeU (y : ℝ) : ℝ := (cutShapeS y)^(2/3:ℝ)

def cutThreshold (n m y : ℝ) : ℝ :=
  (6*n*cubeScale m*(1-cutShapeU y)+2*n*sqrt n*(1-cutShapeS y))/
    (1-(6*n*cubeScale m)*cutShapeU y/(3*m))

theorem cutShapeS_nonneg {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) : 0 ≤ cutShapeS y := by
  unfold cutShapeS
  positivity

theorem cutShapeS_le_one {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) : cutShapeS y ≤ 1 := by
  have h₁ : sqrt y ≤ 1 := (sqrt_le_one).mpr hy₁
  have h₂ : sqrt (1-y) ≤ 1 := (sqrt_le_one).mpr (by linarith)
  have a := mul_le_mul_of_nonneg_left h₁ hy
  have b := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hy₁)
  unfold cutShapeS
  nlinarith

theorem cutShapeU_nonneg {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) : 0 ≤ cutShapeU y :=
  rpow_nonneg (cutShapeS_nonneg hy hy₁) _

theorem cutShapeU_le_one {y : ℝ} (hy : 0 ≤ y) (hy₁ : y ≤ 1) : cutShapeU y ≤ 1 := by
  unfold cutShapeU
  exact rpow_le_one (cutShapeS_nonneg hy hy₁) (cutShapeS_le_one hy hy₁) (by norm_num)

theorem split_order_power {n y : ℝ} (hn : 0 ≤ n) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    (y*n)*sqrt (y*n)+((1-y)*n)*sqrt ((1-y)*n)=n*sqrt n*cutShapeS y := by
  rw [sqrt_mul hy,sqrt_mul (sub_nonneg.mpr hy₁)]
  unfold cutShapeS
  ring

theorem order_power_two_thirds {n : ℝ} (hn : 0 ≤ n) :
    (n*sqrt n)^(2/3:ℝ)=n := by
  rw [← rpow_three_halves hn,← rpow_mul hn]
  norm_num

theorem cubeScale_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cubeScale (a*b)=cubeScale a*cubeScale b := mul_rpow ha hb

theorem cubeScale_sub {m e : ℝ} (hm : 0 < m) (he : e ≤ m) :
    cubeScale (m-e)=cubeScale m*cubeScale (1-e/m) := by
  have hnon : 0 ≤ 1-e/m := by rw [sub_nonneg,div_le_one hm]; exact he
  rw [← cubeScale_mul hm.le hnon]
  congr 1
  field_simp

/-- The two child graphs are allowed to have arbitrary edge densities.
Hölder handles this freedom without assigning each child an assumed density. -/
theorem mixedBudget_split {n m y m₁ m₂ e : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hem : e ≤ m) (hedges : m₁+m₂=m-e) :
    mixedBudget (y*n) m₁+mixedBudget ((1-y)*n) m₂ ≤
      6*n*cubeScale m*cutShapeU y*cubeScale (1-e/m)+2*n*sqrt n*cutShapeS y := by
  have hh := split_cube_budget (mul_nonneg hy hn) (mul_nonneg (sub_nonneg.mpr hy₁) hn) hm₁ hm₂
  rw [split_order_power hn hy hy₁,hedges,cubeScale_sub hm hem,
    mul_rpow (mul_nonneg hn (sqrt_nonneg n)) (cutShapeS_nonneg hy hy₁),
    order_power_two_thirds hn] at hh
  have h6 := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 6)
  have he := split_order_power hn hy hy₁
  unfold mixedBudget cutShapeU
  nlinarith only [h6,he]

theorem cutThreshold_den_pos {n m y : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) (hFB : 6*n*cubeScale m ≤ m) :
    0 < 1-(6*n*cubeScale m)*cutShapeU y/(3*m) := by
  have hmul : (6*n*cubeScale m)*cutShapeU y ≤ m :=
    (mul_le_of_le_one_right (by positivity [cubeScale_pos hm]) (cutShapeU_le_one hy hy₁)).trans hFB
  have hdiv : (6*n*cubeScale m)*cutShapeU y/(3*m) ≤ 1/3 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  linarith

/-- Exact scalar implication used by the graph cut induction. -/
theorem cutThreshold_pays_children {n m y m₁ m₂ e : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy₁ : y ≤ 1) (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (he : 0 ≤ e) (hem : e ≤ m) (hedges : m₁+m₂=m-e)
    (hFB : 6*n*cubeScale m ≤ m) (hcut : e ≤ cutThreshold n m y) :
    mixedBudget (y*n) m₁+mixedBudget ((1-y)*n) m₂+e ≤ mixedBudget n m := by
  have hs := mixedBudget_split hn hm hy hy₁ hm₁ hm₂ hem hedges
  have hp := sparse_cut_payment (by positivity [cubeScale_pos hm])
    (cutShapeU_nonneg hy hy₁) hm he hem (cutThreshold_den_pos hn hm hy hy₁ hFB) hcut
  unfold mixedBudget at hs ⊢
  linarith only [hs,hp]

end
end Cycle13.MixedSample
