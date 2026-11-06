import Cycle12.Foundations.SamplingScale

namespace Cycle13
open Real
noncomputable section

def AnchorParameters.scale (C : AnchorParameters) (s : ℝ) : AnchorParameters where
  δ := s*C.δ
  β := s*C.β
  L := C.L
  lower := s^2*C.lower
  upper := s^2*C.upper
  err := C.err
  miss := C.miss
  cap := s*C.cap
  ω := C.ω
  slope := C.slope
  b := s*C.b
  θ := C.θ
  c := C.c
  popB := s^2*C.popB
  h := s*C.h
  t₀ := C.t₀
  κ := C.κ
  τ := C.τ

theorem AnchorParameters.valid_scale (C : AnchorParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ))
    (hcap : 0 < C.cap) (hb : 0 ≤ C.b) :
    (C.scale s).Valid p (scaledMark q s hs) ρ' (s^2*n) := by
  have hs0 : 0 < s := by linarith
  have hss : s ≤ s^2 := by nlinarith
  have hn : 0 < n := (mul_pos (by norm_num : (0:ℝ) < 9) hC.scale_pos).trans_le hC.order_scale
  have hδ : C.δ ≤ s*C.δ := by nlinarith [hC.degree_pos]
  have hqδ : (scaledMark q s hs:ℝ)*(s*C.δ)=(q:ℝ)*C.δ := by
    rw [← mul_assoc,scaledMark_mul]
  have hqu : (scaledMark q s hs:ℝ)*(s^2*C.upper)=s*((q:ℝ)*C.upper) := by
    change ((q:ℝ)/s)*(s^2*C.upper)=_
    field_simp <;> ring
  have hmean : (2+((s*C.δ)/(s*C.β))*exp (-(scaledMark q s hs:ℝ)*(s*C.δ)))/C.err=
      (2+(C.δ/C.β)*exp (-(q:ℝ)*C.δ))/C.err := by
    rw [neg_mul,hqδ,← neg_mul,mul_div_mul_left _ _ hs0.ne']
  have hmiss : (C.L/(s*C.δ)+exp (-(scaledMark q s hs:ℝ)*(s*C.δ)))/C.miss ≤
      (C.L/C.δ+exp (-(q:ℝ)*C.δ))/C.miss := by
    rw [neg_mul,hqδ,← neg_mul]
    exact div_le_div_of_nonneg_right (add_le_add
      (div_le_div_of_nonneg_left hC.anchor_pos.le hC.degree_pos hδ) le_rfl) hC.miss_pos.le
  have htail : exp (-((s*C.cap)-(scaledMark q s hs:ℝ)*(s^2*C.upper))^2/(2*(s*C.cap))) ≤
      exp (-(C.cap-(q:ℝ)*C.upper)^2/(2*C.cap)) := by
    rw [hqu]
    exact witness_mark_tail_scaled hs hcap
  have hret : 1-C.h/n-C.cap/C.h ≤ 1-(s*C.h)/(s^2*n)-(s*C.cap)/(s*C.h) := by
    have hsN : n ≤ s*n := by nlinarith
    have hh := div_le_div_of_nonneg_left hC.scale_pos.le hn hsN
    have he : (s*C.h)/(s^2*n)=C.h/(s*n) := by field_simp <;> ring
    rw [he,mul_div_mul_left _ _ hs0.ne']
    linarith
  refine {
    p_pos := hC.p_pos
    residual_pos := hC.residual_pos.trans_le hρ
    degree_pos := mul_pos hs0 hC.degree_pos
    expansion_pos := mul_pos hs0 hC.expansion_pos
    anchor_pos := hC.anchor_pos
    anchor_lt_degree := hC.anchor_lt_degree.trans_le hδ
    error_pos := hC.error_pos
    miss_pos := hC.miss_pos
    mark_degree := by simpa only [scale,hqδ] using hC.mark_degree
    mark_cap := by simpa only [scale,hqu] using mul_le_mul_of_nonneg_left hC.mark_cap hs0.le
    witness_pos := hC.witness_pos
    witness_bound := ?_
    slope_pos := hC.slope_pos
    theta_pos := hC.theta_pos
    mgf_slope := hC.mgf_slope
    population_pos := hC.population_pos
    population_first := hC.population_first
    population_second := ?_
    population_bound := ?_
    scale_pos := mul_pos hs0 hC.scale_pos
    order_scale := ?_
    side_scale_lower := hC.side_scale_lower
    side_scale_bound := ?_
    retained_nonneg := hC.retained_nonneg
    marked_retention := hC.marked_retention.trans hret
    fraction_nonneg := hC.fraction_nonneg
    fraction_le_one := hC.fraction_le_one
    cut_threshold := ?_ }
  · dsimp only [scale]
    rw [hmean]
    linarith [hC.witness_bound]
  · dsimp only [scale]
    have hh := mul_le_mul_of_nonneg_left hC.population_second (sq_nonneg s)
    nlinarith
  · dsimp only [scale]
    have he : C.err*C.L*(s^2*n)/(s*C.δ)=s*(C.err*C.L*n/C.δ) := by field_simp <;> ring
    rw [he]
    have hcost : 0 ≤ C.err*C.L*n/C.δ := div_nonneg
      (mul_nonneg (mul_nonneg hC.error_pos.le hC.anchor_pos.le) hn.le) hC.degree_pos.le
    have h₁ := mul_le_mul_of_nonneg_left hC.population_bound (sq_nonneg s)
    have h₂ := mul_le_mul_of_nonneg_right hss hb
    have h₃ := mul_le_mul_of_nonneg_right hss hcost
    nlinarith
  · dsimp only [scale]
    have hh := mul_le_mul_of_nonneg_left hC.order_scale hs0.le
    have hh' := mul_le_mul_of_nonneg_right hss hn.le
    nlinarith
  · dsimp only [scale]
    have h₁ := mul_le_mul_of_nonneg_left hC.side_scale_bound hs0.le
    have h₂ : C.c*(s*(C.β*(C.δ-C.L)/C.L)) ≤ C.c*((s*C.β)*(s*C.δ-C.L)/C.L) := by
      apply mul_le_mul_of_nonneg_left _ hC.population_pos.le
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hC.anchor_pos.le
      nlinarith [mul_le_mul_of_nonneg_left hδ (mul_nonneg hs0.le hC.expansion_pos.le)]
    nlinarith
  · dsimp only [scale]
    have hbase : 0 ≤ C.τ*C.κ*C.h*C.c*(ρ:ℝ)^2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.fraction_nonneg hC.retained_nonneg)
        hC.scale_pos.le) hC.population_pos.le) (sq_nonneg _)
    have h₁ := mul_le_mul_of_nonneg_right hs hbase
    have hr := pow_le_pow_left₀ ρ.2.1 hρ 2
    have h₂ := mul_le_mul_of_nonneg_left hr
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs0.le hC.fraction_nonneg)
        hC.retained_nonneg) hC.scale_pos.le) hC.population_pos.le)
    nlinarith [hC.cut_threshold]

end
end Cycle13
