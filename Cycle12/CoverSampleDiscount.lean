import Cycle12.CoverBudgetBounds

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

/-- The loss from flooring the sample order still leaves enough cycle discount
uniformly on the whole hard-case range, including x tending to zero. -/
theorem cover_sample_order_discount {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hsize : 2*m ≤ n^2) (hxmax : coverGraphX n m ≤ 17/250) :
    (47/100)*coverScaleW (coverGraphX n m)*n ≤
      (⌊coverSampleP (coverGraphX n m)*n⌋₊:ℝ) := by
  let x := coverGraphX n m
  let w := coverScaleW x
  have hx : 0 < x := cover_graph_x_pos hn hm
  have hw : 0 < w := cover_w_pos hx
  have hs := sOf_ge_one hm hsize
  have hs2 : 1 ≤ (sOf n m)^2 := by nlinarith
  have hwmax : w ≤ coverScaleW (17/250) := cover_w_mono hx.le hxmax
  have hw2 : w^2 ≤ (coverScaleW (17/250))^2 := pow_le_pow_left₀ hw.le hwmax 2
  have hcoord : n=4*(43/10)^3*(sOf n m)^2/w^3 := (cover_graph_coordinates_exact hn hm).1
  have hnw : n*w=4*(43/10)^3*(sOf n m)^2/w^2 := by
    calc
      n*w=(4*(43/10)^3*(sOf n m)^2/w^3)*w := congrArg (fun y => y*w) hcoord
      _=4*(43/10)^3*(sOf n m)^2/w^2 := by field_simp
  have hlarge : 40 ≤ n*w := by
    rw [hnw]
    apply (le_div_iff₀ (pow_pos hw 2)).mpr
    have hconst : 40*(coverScaleW (17/250))^2 ≤ 4*(43/10:ℝ)^3 := by norm_num [coverScaleW]
    nlinarith only [hw2,hconst,hs2]
  have hp := cover_p0_lower hx.le
  have hfloor := (Nat.sub_one_lt_floor (coverSampleP x*n)).le
  rw [cover_p_w_identity] at hfloor
  have hmul := mul_le_mul_of_nonneg_right hp (mul_pos hw hn).le
  change (47/100)*w*n ≤ (⌊coverSampleP x*n⌋₊:ℝ)
  rw [cover_p_w_identity]
  change w*coverScaleP0 x*n-1 ≤ _ at hfloor
  nlinarith only [hfloor,hmul,hlarge]

theorem cover_sample_count_within_cycle_budget {n m count : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hsize : 2*m ≤ n^2) (hxmax : coverGraphX n m ≤ 17/250)
    (hcount : count ≤ (n-(⌊coverSampleP (coverGraphX n m)*n⌋₊:ℝ))/2) :
    count ≤ coverCycleBudget n m := by
  have hv : coverSampleV (coverGraphX n m) < 1 :=
    (cover_sample_v_half _ (cover_graph_x_pos hn hm).le hxmax).2.trans_lt (by norm_num)
  have hN := cover_sample_order_discount hn hm hsize hxmax
  have hbudget := cover_cycle_budget_lower hn hm hsize hv
  nlinarith only [hcount,hN,hbudget]

end
end Cycle12
