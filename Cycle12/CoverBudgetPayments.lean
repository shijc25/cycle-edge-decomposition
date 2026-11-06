import Cycle12.CoverGraphCoordinates
import Cycle12.Foundations.MixedDeleteBudget

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

def coverCutThreshold (n m y : ℝ) : ℝ :=
  ((43/10)*n*cubeScale m*(1-cutShapeU y)+3*n*sqrt n*(1-cutShapeS y))/
    (1-((43/10)*n*cubeScale m)*cutShapeU y/(3*m))

def coverDeleteThreshold (n m : ℝ) : ℝ :=
  ((43/10)*cubeScale m+(447/100)*sqrt n)/(1-(33/125)*((43/10)*n*cubeScale m)/m)

theorem cover_budget_split {n m y m₁ m₂ e : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hm1 : 0 ≤ m₁) (hm2 : 0 ≤ m₂)
    (hem : e ≤ m) (hedges : m₁+m₂=m-e) :
    coverGraphBudget (y*n) m₁+coverGraphBudget ((1-y)*n) m₂ ≤
      (43/10)*n*cubeScale m*cutShapeU y*cubeScale (1-e/m)+3*n*sqrt n*cutShapeS y := by
  have hh := split_cube_budget (mul_nonneg hy hn) (mul_nonneg (sub_nonneg.mpr hy1) hn) hm1 hm2
  rw [split_order_power hn hy hy1,hedges,cubeScale_sub hm hem,
    mul_rpow (mul_nonneg hn (sqrt_nonneg n)) (cutShapeS_nonneg hy hy1),
    order_power_two_thirds hn] at hh
  have hB := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 43/10)
  have he := split_order_power hn hy hy1
  unfold coverGraphBudget cutShapeU
  nlinarith only [hB,he]

theorem cover_cut_threshold_den_pos {n m y : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hB : (43/10)*n*cubeScale m ≤ m) :
    0 < 1-((43/10)*n*cubeScale m)*cutShapeU y/(3*m) := by
  have hmul : ((43/10)*n*cubeScale m)*cutShapeU y ≤ m :=
    (mul_le_of_le_one_right (by positivity [cubeScale_pos hm]) (cutShapeU_le_one hy hy1)).trans hB
  have hd : ((43/10)*n*cubeScale m)*cutShapeU y/(3*m) ≤ 1/3 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith only [hmul])
  linarith only [hd]

theorem cover_cut_pays_children {n m y m₁ m₂ e : ℝ} (hn : 0 ≤ n) (hm : 0 < m)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (hm1 : 0 ≤ m₁) (hm2 : 0 ≤ m₂)
    (he : 0 ≤ e) (hem : e ≤ m) (hedges : m₁+m₂=m-e)
    (hB : (43/10)*n*cubeScale m ≤ m) (hcut : e ≤ coverCutThreshold n m y) :
    coverGraphBudget (y*n) m₁+coverGraphBudget ((1-y)*n) m₂+e ≤ coverGraphBudget n m := by
  have hs := cover_budget_split hn hm hy hy1 hm1 hm2 hem hedges
  have hp := sparse_cut_payment (by positivity [cubeScale_pos hm])
    (cutShapeU_nonneg hy hy1) hm he hem (cover_cut_threshold_den_pos hn hm hy hy1 hB) hcut
  unfold coverGraphBudget at hs ⊢
  linarith only [hs,hp]

theorem cover_delete_threshold_den_pos {n m : ℝ} (hm : 0 < m)
    (hB : (43/10)*n*cubeScale m ≤ m) :
    0 < 1-(33/125)*((43/10)*n*cubeScale m)/m := by
  have hh : (33/125:ℝ)*((43/10)*n*cubeScale m)/m ≤ 33/125 :=
    (div_le_iff₀ hm).mpr (by linarith only [hB])
  linarith only [hh]

theorem cover_delete_pays_vertex {n m j : ℝ} (hn : 100 ≤ n) (hm : 0 < m)
    (hj : 0 ≤ j) (hjm : j ≤ m) (hB : (43/10)*n*cubeScale m ≤ m)
    (hdegree : j ≤ coverDeleteThreshold n m) :
    coverGraphBudget (n-1) (m-j)+j ≤ coverGraphBudget n m := by
  have hn1 : 0 ≤ n-1 := by linarith only [hn]
  have ht := (cubeScale_pos hm).le
  have hroot := cube_deletion_tangent hm hj hjm
  have hrem := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by positivity : 0 ≤ (43/10)*(n-1)) ht)
  have horder := order_deletion_three_halves hn
  have hcut := (le_div_iff₀ (cover_delete_threshold_den_pos hm hB)).mp hdegree
  have hcoeff : (33/125:ℝ)*((43/10)*n*cubeScale m)/m ≤ (43/30)*(n-1)*cubeScale m/m := by
    apply div_le_div_of_nonneg_right _ hm.le
    have hh := mul_le_mul_of_nonneg_right
      (show (33/125:ℝ)*((43/10)*n) ≤ (43/30)*(n-1) by linarith only [hn]) ht
    nlinarith only [hh]
  have hjc := mul_le_mul_of_nonneg_left (sub_le_sub_left hcoeff 1) hj
  unfold coverGraphBudget
  rw [cubeScale_sub hm hjm]
  have hid : (43/10)*(n-1)*cubeScale m*(1-j/(3*m))+j =
      (43/10)*n*cubeScale m-(43/10)*cubeScale m+j*(1-(43/30)*(n-1)*cubeScale m/m) := by ring
  nlinarith only [hrem,horder,hcut,hjc,hid]

end
end Cycle12
