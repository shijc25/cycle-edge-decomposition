import Cycle12.Foundations.MixedGraphCoordinates

namespace Cycle13.MixedSample
open Real
noncomputable section

def mixedBudget (n m : ℝ) : ℝ := 6*n*cubeScale m+2*n*sqrt n

theorem mixedBudget_nonneg {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) : 0 ≤ mixedBudget n m := by
  unfold mixedBudget cubeScale
  positivity

theorem mixedBudget_eq_incident_fraction {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    v (xOf n m)*m=mixedBudget n m := by
  have ht := cubeScale_pos hm
  have hc := cubeScale_cube hm.le
  unfold v
  rw [w_xOf hn.le hm]
  unfold xOf mixedBudget
  generalize he : cubeScale m = t at *
  rw [← hc]
  field_simp <;> ring

theorem sample_fraction_pays_cycle_deficit {x : ℝ} (hx : 0 ≤ x) :
    (47/200:ℝ)*w x ≤ (12/25)*p x := by
  have hP := P_lower hx
  have hw := w_nonneg x
  have hh := mul_le_mul_of_nonneg_left hP hw
  unfold p
  nlinarith

theorem hard_count_budget {n count x s : ℝ} (hx : 0 < x) (hn₀ : 0 ≤ n)
    (hn : n=s^2*order x)
    (hcount : count ≤ (n-(24/25)*(s^2*sampleOrder x))/2) :
    count ≤ (1/2-(47/200)*w x)*n := by
  have hsample : s^2*sampleOrder x=p x*n := by
    rw [hn,← sampleOrder_identity]
    ring
  rw [hsample] at hcount
  have hh := mul_le_mul_of_nonneg_right (sample_fraction_pays_cycle_deficit hx.le) hn₀
  nlinarith

theorem hard_singles_budget {n m singles x s : ℝ} (hx : 0 < x)
    (hm : m=edgeCount x s)
    (hsingles : singles ≤ v x*edgeCount x s+n-(24/25)*(s^2*sampleOrder x)) :
    singles ≤ v x*m+n := by
  have hp : 0 ≤ (24/25:ℝ)*(s^2*sampleOrder x) := by positivity [sampleOrder_pos hx]
  rw [hm]
  linarith

theorem hard_order_large {x s : ℝ} (hx : 0 < x) (hxm : x ≤ xmax) (hs : 1 ≤ s) :
    100 < s^2*order x := by
  have hh := order_antitone hx hxm
  have ho := order_pos hx
  have hs₂ : 1 ≤ s^2 := by nlinarith
  have hn := mul_le_mul_of_nonneg_right hs₂ ho.le
  have hbase : (100:ℝ) < order xmax := by norm_num [order,w,xmax]
  nlinarith

theorem hard_fraction_lt_one {x : ℝ} (hx : 0 ≤ x) (hxm : x ≤ xmax) : v x < 1 := by
  have hh := v_mono hx hxm
  have hbase : v xmax < 1 := by norm_num [v,w,xmax]
  exact hh.trans_lt hbase

end
end Cycle13.MixedSample
