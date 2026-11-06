import Cycle12.Foundations.MixedCycleBudget

namespace Cycle13
open Real Set
noncomputable section

/-- The density-dependent part of a finite-stage block payment. -/
def densityFee (a b t : ℝ) : ℝ := a*t^(1/3:ℝ)-t/2-b*t^(-(1/3:ℝ))

def densityFeeDeriv (a b t : ℝ) : ℝ :=
  (a/3)*t^(-(2/3:ℝ))-1/2+(b/3)*t^(-(4/3:ℝ))

theorem densityFee_hasDeriv {a b t : ℝ} (ht : 0<t) :
    HasDerivAt (densityFee a b) (densityFeeDeriv a b t) t := by
  have h₁ := hasDerivAt_rpow_const (p:=(1/3:ℝ)) (Or.inl ht.ne')
  have h₂ := hasDerivAt_rpow_const (p:=-(1/3:ℝ)) (Or.inl ht.ne')
  have hh := ((h₁.const_mul a).sub ((hasDerivAt_id t).div_const 2)).sub (h₂.const_mul b)
  unfold densityFee densityFeeDeriv
  convert hh using 1 <;> norm_num
  all_goals first | (funext x; simp only [Pi.sub_apply,id_eq]) | ring

/-- Concavity on the entire positive half-line, not on a sampled grid. -/
theorem densityFee_concave {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    ConcaveOn ℝ (Ioi 0) (densityFee a b) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi (0:ℝ))
    (fun t ht => (densityFee_hasDeriv ht).continuousAt.continuousWithinAt)
    (fun t ht => (densityFee_hasDeriv (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  have hx₀ : 0<x := interior_subset hx
  have hy₀ : 0<y := interior_subset hy
  rw [(densityFee_hasDeriv hx₀).deriv,(densityFee_hasDeriv hy₀).deriv]
  have h₁ := rpow_le_rpow_of_nonpos hx₀ hxy (by norm_num : -(2/3:ℝ)≤0)
  have h₂ := rpow_le_rpow_of_nonpos hx₀ hxy (by norm_num : -(4/3:ℝ)≤0)
  have hA := mul_le_mul_of_nonneg_left h₁ (by positivity : 0≤a/3)
  have hB := mul_le_mul_of_nonneg_left h₂ (by positivity : 0≤b/3)
  unfold densityFeeDeriv
  linarith

theorem concave_tangent_upper {S : Set ℝ} {f : ℝ → ℝ} {a t d : ℝ}
    (hf : ConcaveOn ℝ S f) (ha : a∈S) (ht : t∈S) (hd : HasDerivAt f d a) :
    f t ≤ f a+d*(t-a) := by
  rcases lt_trichotomy a t with h | rfl | h
  · have hh := hf.slope_le_of_hasDerivAt ha ht h hd
    rw [slope_def_field] at hh
    have he := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := hf.le_slope_of_hasDerivAt ht ha h hd
    rw [slope_def_field] at hh
    have he := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

/-- A rational enclosure of one tangent controls every density above the
lower endpoint. Lower and upper derivative bounds are both used. -/
theorem densityFee_halfline_bound {a b x lower value dlo dhi : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hx : 0<x) (hxl : lower≤x)
    (hv : densityFee a b x ≤ value)
    (hdlo : dlo ≤ densityFeeDeriv a b x)
    (hdhi : densityFeeDeriv a b x ≤ dhi) (hdhi₀ : dhi≤0)
    {t : ℝ} (ht : 0<t) (htl : lower≤t) :
    densityFee a b t ≤ value+dlo*(lower-x) := by
  have hh := concave_tangent_upper (densityFee_concave ha hb) hx ht (densityFee_hasDeriv hx)
  have hd : densityFeeDeriv a b x ≤ 0 := hdhi.trans hdhi₀
  have h₁ := mul_le_mul_of_nonpos_left (sub_le_sub_right htl x) hd
  have h₂ := mul_le_mul_of_nonpos_right hdlo (sub_nonpos.mpr hxl)
  linarith

theorem densityFee_zero (a b : ℝ) : densityFee a b 0=0 := by
  norm_num [densityFee]

theorem densityFee_component_bound {a x value dlo dhi : ℝ}
    (ha : 0≤a) (hx : 0<x) (hv : densityFee a 0 x ≤ value)
    (hdlo : dlo ≤ densityFeeDeriv a 0 x)
    (hdhi : densityFeeDeriv a 0 x ≤ dhi) (hdhi₀ : dhi≤0)
    {t : ℝ} (ht : 0≤t) : densityFee a 0 t ≤ max 0 (value-dlo*x) := by
  rcases ht.eq_or_lt with he | he
  · rw [← he,densityFee_zero]
    exact le_max_left _ _
  · have hh := densityFee_halfline_bound ha le_rfl hx hx.le hv hdlo hdhi hdhi₀ he ht
    have hh' : densityFee a 0 t ≤ value-dlo*x := by convert hh using 1 <;> ring
    exact hh'.trans (le_max_right _ _)

end
end Cycle13
