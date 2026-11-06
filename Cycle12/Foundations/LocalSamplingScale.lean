import Cycle12.Foundations.SamplingFailureScale

namespace Cycle13
open Real
noncomputable section

def LocalCutParameters.scale (C : LocalCutParameters) (s : ℝ) : LocalCutParameters where
  δ := s*C.δ
  β := s*C.β
  err := s*C.err
  upper := s^2*C.upper
  cap := s*C.cap
  ω := C.ω
  slope := C.slope
  b := s*C.b
  θ := C.θ
  c := C.c
  η := C.η
  size := s^2*C.size
  ν := C.ν
  ell := s^2*C.ell
  α := C.α
  h := s*C.h
  t₀ := C.t₀
  L := C.L
  k₀ := C.k₀
  κ := C.κ
  τ := C.τ

theorem LocalCutParameters.valid_scale (C : LocalCutParameters)
    {p q ρ ρ' : unitInterval} {s : ℝ}
    (hC : C.Valid p q ρ) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ))
    (hcap : 0 < C.cap) (hsize : C.cap ≤ C.size) :
    (C.scale s).Valid p (scaledMark q s hs) ρ' := by
  have hs0 : 0 < s := by linarith
  have hqδ : (scaledMark q s hs:ℝ)*(s*C.δ)=(q:ℝ)*C.δ := by
    rw [← mul_assoc,scaledMark_mul]
  have hqu : (scaledMark q s hs:ℝ)*(s^2*C.upper)=s*((q:ℝ)*C.upper) := by
    change ((q:ℝ)/s)*(s^2*C.upper)=_
    field_simp <;> ring
  have herr : (2*(s*C.β)+(s*C.δ)*exp (-(scaledMark q s hs:ℝ)*(s*C.δ)))/(s*C.err)=
      (2*C.β+C.δ*exp (-(q:ℝ)*C.δ))/C.err := by
    rw [neg_mul,hqδ,← neg_mul]
    field_simp <;> ring
  have htail : exp (-((s*C.cap)-(scaledMark q s hs:ℝ)*(s^2*C.upper))^2/(2*(s*C.cap))) ≤
      exp (-(C.cap-(q:ℝ)*C.upper)^2/(2*C.cap)) := by
    rw [hqu]
    exact witness_mark_tail_scaled hs hcap
  have hpop : C.slope*(p:ℝ)*C.c+(s*C.err)/(s*C.δ)+(s*C.b)/(s*C.δ-s*C.β)=
      C.slope*(p:ℝ)*C.c+C.err/C.δ+C.b/(C.δ-C.β) := by field_simp <;> ring
  have hret : C.k₀-(C.cap/C.h)*(C.L+1/(C.t₀*C.h)) ≤
      C.k₀-((s*C.cap)/(s*C.h))*(C.L+1/(C.t₀*(s*C.h))) := by
    rw [mul_div_mul_left _ _ hs0.ne']
    have hh : C.t₀*C.h ≤ C.t₀*(s*C.h) := by
      have hp := mul_le_mul_of_nonneg_right hs (mul_pos hC.side_scale_pos hC.scale_pos).le
      nlinarith
    have hi := one_div_le_one_div_of_le (mul_pos hC.side_scale_pos hC.scale_pos) hh
    have hi' : C.L+1/(C.t₀*(s*C.h)) ≤ C.L+1/(C.t₀*C.h) := by linarith
    have hm := mul_le_mul_of_nonneg_left hi' (div_nonneg hcap.le hC.scale_pos.le)
    linarith
  refine {
    p_pos := hC.p_pos
    residual_pos := hC.residual_pos.trans_le hρ
    degree_pos := mul_pos hs0 hC.degree_pos
    cut_lt_degree := mul_lt_mul_of_pos_left hC.cut_lt_degree hs0
    error_pos := mul_pos hs0 hC.error_pos
    mark_degree := by simpa only [scale,hqδ] using hC.mark_degree
    mark_cap := by simpa only [scale,hqu] using mul_le_mul_of_nonneg_left hC.mark_cap hs0.le
    witness_pos := hC.witness_pos
    witness_bound := ?_
    slope_pos := hC.slope_pos
    intercept_nonneg := mul_nonneg hs0.le hC.intercept_nonneg
    theta_pos := hC.theta_pos
    mgf_slope := hC.mgf_slope
    population_pos := hC.population_pos
    population_bound := by simpa only [scale,hpop] using hC.population_bound
    scale_pos := mul_pos hs0 hC.scale_pos
    side_scale_pos := hC.side_scale_pos
    side_scale_bound := ?_
    cap_scale := hC.cap_scale
    profile_retention := hC.profile_retention
    retained_nonneg := hC.retained_nonneg
    marked_retention := hC.marked_retention.trans hret
    fraction_nonneg := hC.fraction_nonneg
    fraction_le_one := hC.fraction_le_one
    cut_threshold := ?_
    small_fraction_nonneg := hC.small_fraction_nonneg
    reverse_nonneg := hC.reverse_nonneg
    reverse_le_one := hC.reverse_le_one
    reverse_mean := ?_
    localization := ?_ }
  · dsimp only [scale]
    rw [herr]
    linarith [hC.witness_bound]
  · dsimp only [scale]
    have hh := mul_le_mul_of_nonneg_left hC.side_scale_bound hs0.le
    nlinarith
  · dsimp only [scale]
    have hh := mul_le_mul_of_nonneg_left hC.cut_threshold hs0.le
    have hr := pow_le_pow_left₀ ρ.2.1 hρ 2
    have hp := mul_le_mul_of_nonneg_left hr
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs0.le hC.fraction_nonneg)
        hC.retained_nonneg) hC.scale_pos.le) hC.population_pos.le)
    nlinarith
  · dsimp only [scale]
    have h₁ := mul_le_mul_of_nonneg_left hC.reverse_mean (sq_nonneg s)
    have hgap : s^2*(C.size-C.cap) ≤ s^2*C.size-s*C.cap := by
      have hh := mul_le_mul_of_nonneg_right (show s ≤ s^2 by nlinarith) hcap.le
      nlinarith
    have hg0 : 0 ≤ s^2*(C.size-C.cap) := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hsize)
    have h₂ := mul_le_mul hρ hgap hg0 ρ'.2.1
    nlinarith
  · dsimp only [scale]
    rw [mul_div_mul_left _ _ hs0.ne']
    have hh := mul_lt_mul_of_pos_left hC.localization (sq_pos_of_pos hs0)
    nlinarith

theorem local_janson_kernel_scale {c u x x' s base : ℝ}
    (hc : 0 ≤ c) (hu : 0 < u) (hx : 0 < x) (hs : 1 ≤ s)
    (hb : 0 < base) (hxx : s*x ≤ x') :
    s*(c*x/(2*(base+1/(u*x)))) ≤ c*x'/(2*(base+1/(u*x'))) := by
  have hxx' : x ≤ x' := by nlinarith
  have hx' : 0 < x' := hx.trans_le hxx'
  have hden := one_div_le_one_div_of_le (mul_pos hu hx) (mul_le_mul_of_nonneg_left hxx' hu.le)
  have hnum : s*(c*x) ≤ c*x' := by nlinarith [mul_le_mul_of_nonneg_left hxx hc]
  calc
    _ = (s*(c*x))/(2*(base+1/(u*x))) := (mul_div_assoc ..).symm
    _ ≤ (c*x')/(2*(base+1/(u*x))) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hc hx'.le) (by positivity) (by linarith)

theorem LocalCutParameters.jansonRate_scale (C : LocalCutParameters)
    {p q ρ ρ' : unitInterval} {s : ℝ}
    (hC : C.Valid p q ρ) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ)) :
    s*C.jansonRate ρ ≤ (C.scale s).jansonRate ρ' := by
  have hb : s*(C.h*(ρ:ℝ)) ≤ (s*C.h)*(ρ':ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hρ (mul_nonneg (by linarith : 0 ≤ s) hC.scale_pos.le)
    nlinarith
  have hk := local_janson_kernel_scale (mul_nonneg (sq_nonneg (1-C.τ)) hC.retained_nonneg)
    hC.side_scale_pos (mul_pos hC.scale_pos hC.residual_pos) hs
    (by linarith [hC.cap_scale] : 0 < C.L+1) hb
  unfold jansonRate scale
  convert hk using 1 <;> ring

theorem LocalCutParameters.failureBound_scale (C : LocalCutParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ))
    (hell : 0 ≤ C.ell) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤
      (exp (s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n))+
        exp (s*(-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n))+
        exp (s*(-(1-C.ν)^2*C.ell/2+(p:ℝ)*(q:ℝ)*n)))/C.ω := by
  have hs0 : 0 < s := by linarith
  have hJ := C.jansonRate_scale hC hs hρ
  have hmgf : -(C.scale s).θ*(C.scale s).b+(p:ℝ)*(scaledMark q s hs:ℝ)*
      exp ((C.scale s).θ*(1-(C.scale s).slope*(p:ℝ)))*(s^2*n)=
      s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n) := by
    dsimp only [scale,scaledMark]
    field_simp <;> ring
  have hent : (p:ℝ)*(scaledMark q s hs:ℝ)*(s^2*n)=s*((p:ℝ)*(q:ℝ)*n) := by
    dsimp only [scaledMark]
    field_simp <;> ring
  have hrev : -(1-C.ν)^2*(s^2*C.ell)/2 ≤ s*(-(1-C.ν)^2*C.ell/2) := by
    have hh := mul_le_mul_of_nonneg_right (show s ≤ s^2 by nlinarith)
      (mul_nonneg (sq_nonneg (1-C.ν)) hell)
    nlinarith
  unfold failureBound
  rw [hmgf,hent]
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add
  · apply add_le_add le_rfl
    exact exp_le_exp.mpr (by linarith)
  · dsimp only [scale]
    exact exp_le_exp.mpr (by linarith)

end
end Cycle13
