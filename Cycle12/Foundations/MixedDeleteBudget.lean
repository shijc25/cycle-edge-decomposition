import Cycle12.Foundations.MixedSplitBudget

namespace Cycle13.MixedSample
open Real
noncomputable section

def deleteThreshold (n m : ℝ) : ℝ :=
  (6*cubeScale m+(149/50)*sqrt n)/(1-(33/125)*(6*n*cubeScale m)/m)

theorem order_deletion_three_halves {n : ℝ} (hn : 100 ≤ n) :
    (n-1)*sqrt (n-1) ≤ (n-149/100)*sqrt n := by
  have hn₀ : 0 ≤ n := by linarith
  have hn₁ : 0 ≤ n-1 := by linarith
  have ha : 0 ≤ (n-1)*sqrt (n-1) := by positivity
  have hb : 0 ≤ (n-149/100)*sqrt n := mul_nonneg (by linarith) (sqrt_nonneg n)
  apply (sq_le_sq₀ ha hb).mp
  rw [mul_pow,mul_pow,sq_sqrt hn₁,sq_sqrt hn₀]
  have hpoly : 0 ≤ (n-100)*n := mul_nonneg (sub_nonneg.mpr hn) hn₀
  nlinarith

theorem deleteThreshold_den_pos {n m : ℝ} (hm : 0 < m)
    (hFB : 6*n*cubeScale m ≤ m) :
    0 < 1-(33/125)*(6*n*cubeScale m)/m := by
  have hh : (33/125:ℝ)*(6*n*cubeScale m)/m ≤ 33/125 :=
    (div_le_iff₀ hm).mpr (by linarith)
  linarith

/-- The exact 1.49 order-loss estimate pays for every deleted edge. This
lemma uses the actual remaining edge count `m-j`, including the zero case. -/
theorem deleteThreshold_pays_vertex {n m j : ℝ} (hn : 100 ≤ n) (hm : 0 < m)
    (hj : 0 ≤ j) (hjm : j ≤ m) (hFB : 6*n*cubeScale m ≤ m)
    (hdegree : j ≤ deleteThreshold n m) :
    mixedBudget (n-1) (m-j)+j ≤ mixedBudget n m := by
  have hn₁ : 0 ≤ n-1 := by linarith
  have ht := (cubeScale_pos hm).le
  have hroot := cube_deletion_tangent hm hj hjm
  have hrem := mul_le_mul_of_nonneg_left hroot (mul_nonneg (by nlinarith : 0 ≤ 6*(n-1)) ht)
  have horder := order_deletion_three_halves hn
  have hcut := (le_div_iff₀ (deleteThreshold_den_pos hm hFB)).mp hdegree
  have hcoeff : (33/125:ℝ)*(6*n*cubeScale m)/m ≤ 2*(n-1)*cubeScale m/m := by
    apply div_le_div_of_nonneg_right _ hm.le
    have hh := mul_le_mul_of_nonneg_right
      (show (33/125:ℝ)*(6*n) ≤ 2*(n-1) by linarith) ht
    nlinarith only [hh]
  have hjc := mul_le_mul_of_nonneg_left (sub_le_sub_left hcoeff 1) hj
  unfold mixedBudget
  rw [cubeScale_sub hm hjm]
  have hid : 6*(n-1)*cubeScale m*(1-j/(3*m))+j =
      6*n*cubeScale m-6*cubeScale m+j*(1-2*(n-1)*cubeScale m/m) := by ring
  nlinarith only [hrem,horder,hcut,hjc,hid]

end
end Cycle13.MixedSample
