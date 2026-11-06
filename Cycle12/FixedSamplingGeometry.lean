import Cycle12.FixedSamplingParameter

namespace Cycle12
noncomputable section

theorem fixed_sampling_parameter_pos (n k : ℕ) (hk : k ≤ n) (hk0 : 0 < k) :
    0 < (fixedSamplingParameter n k hk:ℝ) := by
  have hn : 0 < n := hk0.trans_le hk
  change 0 < (k:ℝ)/(n:ℝ)
  exact div_pos (by exact_mod_cast hk0) (by exact_mod_cast hn)

theorem rounded_mark_count_bounds {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R) :
    q ≤ (⌈q*R⌉₊:ℝ)/R ∧ (⌈q*R⌉₊:ℝ)/R ≤ q+1/R := by
  constructor
  · exact (le_div_iff₀ hR).mpr (Nat.le_ceil _)
  · apply (div_le_iff₀ hR).mpr
    have hb := (Nat.ceil_lt_add_one (mul_nonneg hq hR.le)).le
    have he : (q+1/R)*R=q*R+1 := by field_simp
    rwa [he]

theorem rounded_marks_lt_sample {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R) (N : ℕ)
    (hbudget : q+1/R < (N:ℝ)/R) : ⌈q*R⌉₊ < N := by
  have hh := (rounded_mark_count_bounds hq hR).2.trans_lt hbudget
  have hc := (div_lt_div_iff_of_pos_right hR).mp hh
  exact_mod_cast hc

theorem residual_sampling_ratio_identity (n N t : ℕ) (hN : N ≤ n) (ht : t < N)
    {R : ℝ} (hR : 0 < R) :
    (((N-t:ℕ):ℝ)/(n-t:ℕ))/( (N:ℝ)/n ) =
      ((N:ℝ)/R-(t:ℝ)/R)/((N:ℝ)/R-((N:ℝ)/n)*((t:ℝ)/R)) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt ht))
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (ht.trans_le hN)))
  rw [Nat.cast_sub ht.le,Nat.cast_sub (ht.le.trans hN)]
  have hnt : (n:ℝ)-(t:ℝ)≠0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast (ht.trans_le hN)))
  field_simp
  <;> ring

theorem residual_ratio_mark_mono {z p m M : ℝ} (hz : 0 < z) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm0 : 0 ≤ m) (hm : m ≤ M) (hMz : M < z) :
    (z-M)/(z-p*M) ≤ (z-m)/(z-p*m) := by
  have hM0 : 0 ≤ M := hm0.trans hm
  have hpm := mul_le_mul_of_nonneg_right hp1 hm0
  have hpM := mul_le_mul_of_nonneg_right hp1 hM0
  have hdM : 0 < z-p*M := by nlinarith
  have hdm : 0 < z-p*m := by nlinarith
  apply (div_le_div_iff₀ hdM hdm).mpr
  have hh : 0 ≤ z*(M-m)*(1-p) := mul_nonneg (mul_nonneg hz.le (sub_nonneg.mpr hm))
    (sub_nonneg.mpr hp1)
  nlinarith only [hh]

theorem residual_ratio_population_lower {z pl p m M : ℝ}
    (hz : 0 < z) (hpl0 : 0 ≤ pl) (hpl : pl ≤ p) (hp1 : p ≤ 1)
    (hm0 : 0 ≤ m) (hm : m ≤ M) (hMz : M < z) :
    (z-M)/(z-pl*M) ≤ (z-m)/(z-p*m) := by
  have hp0 : 0 ≤ p := hpl0.trans hpl
  have hM0 : 0 ≤ M := hm0.trans hm
  have hpM := mul_le_mul_of_nonneg_right hp1 hM0
  have hd : 0 < z-p*M := by nlinarith
  have hden : z-p*M ≤ z-pl*M := by nlinarith [mul_le_mul_of_nonneg_right hpl hM0]
  exact (div_le_div_of_nonneg_left (sub_pos.mpr hMz).le hd hden).trans
    (residual_ratio_mark_mono hz hp0 hp1 hm0 hm hMz)

end
end Cycle12
