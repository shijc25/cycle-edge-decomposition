import Cycle12.FixedChooseMoments

namespace Cycle12
noncomputable section

theorem fixed_internal_mean_relative (n k : ℕ) (hn : 1 < n) (hk : 0 < k) :
    fixedChooseRatio n k 2=((k:ℝ)/n)^2*
      (1-(1-(k:ℝ)/n)/((k:ℝ)*(1-1/(n:ℝ)))) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hn1 : (n:ℝ)-1≠0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [fixed_choose_ratio_two]
  field_simp
  <;> ring

theorem fixed_internal_mean_gap (n k : ℕ) (hn : 1 < n) (hk : 0 < k)
    {m alpha : ℝ} (hm : 0 ≤ m) :
    ((1-alpha)-1/((k:ℝ)*(1-1/(n:ℝ))))*(((k:ℝ)/n)^2*m) ≤
      m*fixedChooseRatio n k 2-alpha*((k:ℝ)/n)^2*m := by
  have hn1 : (1:ℝ) < n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hn1]
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hsub : 0 < 1-1/(n:ℝ) := sub_pos.mpr ((div_lt_one hn0).mpr hn1)
  have hden := mul_pos hk0 hsub
  have hp : 0 ≤ (k:ℝ)/n := by positivity
  have hfrac : (1-(k:ℝ)/n)/((k:ℝ)*(1-1/(n:ℝ))) ≤ 1/((k:ℝ)*(1-1/(n:ℝ))) :=
    div_le_div_of_nonneg_right (by linarith only [hp]) hden.le
  have hh := mul_le_mul_of_nonneg_right hfrac (mul_nonneg (sq_nonneg ((k:ℝ)/n)) hm)
  rw [fixed_internal_mean_relative n k hn hk]
  nlinarith only [hh]

theorem fixed_incident_mean_relative (n k : ℕ) (hn : 1 < n) (hk : k ≤ n) :
    1-fixedChooseRatio n (n-k) 2=
      2*((k:ℝ)/n)-((k:ℝ)/n)^2+((k:ℝ)/n)*(1-(k:ℝ)/n)/((n:ℝ)-1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hn1 : (n:ℝ)-1≠0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hn))
  rw [fixed_choose_ratio_two,Nat.cast_sub hk]
  field_simp
  <;> ring

theorem fixed_incident_mean_gap (n k : ℕ) (hn : 1 < n) (hk : k ≤ n)
    {v p0 : ℝ} (hp : (k:ℝ)/n ≤ p0) (hp1 : p0 ≤ 1) :
    v-2*p0+p0^2-p0/((n:ℝ)-1) ≤ v-(1-fixedChooseRatio n (n-k) 2) := by
  have hp0 : 0 ≤ (k:ℝ)/n := by positivity
  have hn1 : (0:ℝ) < (n:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hn)
  have hh := mul_nonneg (sub_nonneg.mpr hp)
    (show 0 ≤ 2-(k:ℝ)/n-p0 by linarith only [hp,hp1])
  have hfrac := div_le_div_of_nonneg_right
    (show ((k:ℝ)/n)*(1-(k:ℝ)/n) ≤ p0 by nlinarith [sq_nonneg ((k:ℝ)/n)]) hn1.le
  rw [fixed_incident_mean_relative n k hn hk]
  nlinarith only [hh,hfrac]

end
end Cycle12
