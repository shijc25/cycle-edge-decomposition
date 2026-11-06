import Cycle12.FixedSamplingParameter

namespace Cycle12
noncomputable section

def coverSampleV (x : ℝ) : ℝ := (43/10)^3*x^2*(1+3*x)
def coverSampleP (x : ℝ) : ℝ := coverSampleV x*(99/200+11/100*coverSampleV x+7/100*(coverSampleV x)^2)

theorem cover_sample_v_half (x : ℝ) (hx0 : 0≤x) (hx1 : x≤17/250) :
    0≤coverSampleV x ∧ coverSampleV x≤1/2 := by
  have h0 : 0≤coverSampleV x := by unfold coverSampleV; positivity
  refine ⟨h0,?_⟩
  calc
    coverSampleV x ≤ (43/10:ℝ)^3*(17/250)^2*(1+3*(17/250)) := by
      unfold coverSampleV
      gcongr
    _ ≤ 1/2 := by norm_num

/-- The full accepted sampling x-range is below one half; consequently
the proved half-range binomial median is sufficient for these parameters. -/
theorem cover_sample_p_lt_half (x : ℝ) (hx0 : 0≤x) (hx1 : x≤17/250) :
    0≤coverSampleP x ∧ coverSampleP x<1/2 := by
  obtain ⟨hv0,hv1⟩ := cover_sample_v_half x hx0 hx1
  have h0 : 0≤coverSampleP x := by unfold coverSampleP; positivity
  refine ⟨h0,?_⟩
  have hh : coverSampleP x ≤ (1/2:ℝ)*(99/200+11/100*(1/2)+7/100*(1/2)^2) := by
    unfold coverSampleP
    gcongr
  norm_num at hh
  linarith

theorem cover_sample_floor_half (r : ℕ) (x : ℝ) (hx0 : 0≤x) (hx1 : x≤17/250) :
    2*⌊coverSampleP x*(r:ℝ)⌋₊≤r := by
  obtain ⟨hp0,hp1⟩ := cover_sample_p_lt_half x hx0 hx1
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg _
  have hn := Nat.floor_le (mul_nonneg hp0 hr0)
  have hp := mul_le_mul_of_nonneg_right hp1.le hr0
  have hh : 2*(⌊coverSampleP x*(r:ℝ)⌋₊:ℝ)≤r := by nlinarith
  exact_mod_cast hh

theorem cover_sample_residual_half (r t : ℕ) (x : ℝ)
    (hx0 : 0≤x) (hx1 : x≤17/250) (ht : t≤⌊coverSampleP x*(r:ℝ)⌋₊) :
    2*(⌊coverSampleP x*(r:ℝ)⌋₊-t)≤r-t :=
  fixed_sampling_residual_half _ _ _ ht (cover_sample_floor_half r x hx0 hx1)

end
end Cycle12
