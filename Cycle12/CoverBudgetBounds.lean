import Cycle12.CoverGreedyLog

namespace Cycle12
open Real Cycle13.MixedSample
noncomputable section

theorem cover_graph_budget_nonneg {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) :
    0 ≤ coverGraphBudget n m := by unfold coverGraphBudget cubeScale; positivity

theorem cover_v_pos {x : ℝ} (hx : 0 < x) : 0 < coverSampleV x := by
  unfold coverSampleV
  positivity

theorem cover_w_lt_one_of_fraction {x : ℝ} (hx : 0 ≤ x) (hv : coverSampleV x < 1) :
    coverScaleW x < 1 := by
  rw [cover_v_w_identity] at hv
  have hw := cover_w_nonneg x
  nlinarith

theorem cover_normalized_density {n m : ℝ} (hn : 0 < n) (hm : 0 < m) :
    m/(2*(43/10)^3*n)=sOf n m/(coverScaleW (coverGraphX n m))^3 := by
  have ht := cubeScale_pos hm
  have hc := cubeScale_cube hm.le
  rw [cover_graph_w_identity hn.le hm]
  unfold sOf
  generalize he : cubeScale m=t at *
  rw [← hc]
  field_simp
  <;> ring

theorem cover_scale_deficit_le {w s : ℝ} (hw : 0 < w) (hs : 1 ≤ s) :
    (s/w^3)^(-(1/3:ℝ)) ≤ w := by
  have hsp : 0 < s := by linarith
  have hu : 0 < s/w^3 := by positivity
  have hp := rpow_nonneg hu.le (-(1/3:ℝ))
  apply (pow_le_pow_iff_left₀ hp hw.le (by norm_num : (3:ℕ) ≠ 0)).mp
  have he : ((s/w^3)^(-(1/3:ℝ)))^3=w^3/s := by
    rw [← rpow_mul_natCast hu.le]
    norm_num only [Nat.cast_ofNat,neg_div,neg_mul]
    rw [rpow_neg_one]
    field_simp
  rw [he]
  exact (div_le_iff₀ hsp).mpr (by nlinarith [mul_le_mul_of_nonneg_left hs (pow_nonneg hw.le 3)])

theorem cover_cycle_budget_lower {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hsize : 2*m ≤ n^2) (hv : coverSampleV (coverGraphX n m) < 1) :
    (1/2-(47/200)*coverScaleW (coverGraphX n m))*n ≤ coverCycleBudget n m := by
  have hx := cover_graph_x_pos hn hm
  have hw := cover_w_pos hx
  have hwl := cover_w_lt_one_of_fraction hx.le hv
  have hs := sOf_ge_one hm hsize
  have hw3 : (coverScaleW (coverGraphX n m))^3 < 1 := pow_lt_one₀ hw.le hwl (by norm_num)
  have hu : 1 < sOf n m/(coverScaleW (coverGraphX n m))^3 :=
    (one_lt_div (pow_pos hw 3)).mpr (hw3.trans_le hs)
  rw [cover_cycle_budget_eq,cover_normalized_density hn hm]
  unfold cycleFactor
  rw [if_neg (not_le_of_gt hu)]
  have hb := cover_scale_deficit_le hw hs
  nlinarith [mul_le_mul_of_nonneg_left hb hn.le]

theorem cover_nontrivial_order {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hsize : 2*m ≤ n^2) (hv : coverSampleV (coverGraphX n m) < 1) : 100 < n := by
  have hw := cover_w_pos (cover_graph_x_pos hn hm)
  have hwl := cover_w_lt_one_of_fraction (cover_graph_x_pos hn hm).le hv
  have hw3 : (coverScaleW (coverGraphX n m))^3 < 1 := pow_lt_one₀ hw.le hwl (by norm_num)
  have hs := sOf_ge_one hm hsize
  have hs2 : 1 ≤ (sOf n m)^2 := by nlinarith
  have ho : 4*(43/10:ℝ)^3 < n := by
    rw [(cover_graph_coordinates_exact hn hm).1]
    apply (lt_div_iff₀ (pow_pos hw 3)).mpr
    nlinarith only [hw3,hs2]
  linarith only [ho]

theorem cover_greedy_fine_budget {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hsize : 2*m ≤ n^2) (hx : 17/250 ≤ coverGraphX n m)
    (hv : coverSampleV (coverGraphX n m) < 1) :
    m*exp (-2*coverCycleBudget n m/n) ≤ coverGraphBudget n m := by
  have hb := cover_cycle_budget_lower hn hm hsize hv
  have hg := coverGreedyLogGap_nonneg hx hv
  unfold coverGreedyLogGap at hg
  have hlog : -1+(47/100)*coverScaleW (coverGraphX n m) ≤ log (coverSampleV (coverGraphX n m)) := by
    linarith only [hg]
  have hmul := mul_le_mul_of_nonneg_right hlog hn.le
  have hexp : -2*coverCycleBudget n m/n ≤ log (coverSampleV (coverGraphX n m)) :=
    (div_le_iff₀ hn).mpr (by nlinarith only [hb,hmul])
  have hp := exp_le_exp.mpr hexp
  rw [exp_log (cover_v_pos (cover_graph_x_pos hn hm)),← cover_graph_budget_identity hn.le hm] at hp
  have hh := mul_le_mul_of_nonneg_left hp hm.le
  have hid : m*(coverGraphBudget n m/m)=coverGraphBudget n m := mul_div_cancel₀ _ hm.ne'
  rwa [hid] at hh

theorem cover_greedy_coarse_budget {n m : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hx : 17/250 ≤ coverGraphX n m) (hv : coverSampleV (coverGraphX n m) < 1) :
    m*exp (-1) ≤ coverGraphBudget n m := by
  have hg := coverGreedyLogGap_nonneg hx hv
  unfold coverGreedyLogGap at hg
  have hlog : (-1:ℝ) ≤ log (coverSampleV (coverGraphX n m)) := by
    linarith [cover_w_nonneg (coverGraphX n m)]
  have hp := exp_le_exp.mpr hlog
  rw [exp_log (cover_v_pos (cover_graph_x_pos hn hm)),← cover_graph_budget_identity hn.le hm] at hp
  have hh := mul_le_mul_of_nonneg_left hp hm.le
  have hid : m*(coverGraphBudget n m/m)=coverGraphBudget n m := mul_div_cancel₀ _ hm.ne'
  rwa [hid] at hh

end
end Cycle12
