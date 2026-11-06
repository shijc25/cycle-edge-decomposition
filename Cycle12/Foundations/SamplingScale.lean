import Cycle12.Foundations.VertexSamplingCertificate

namespace Cycle13
open Real
noncomputable section

def scaledMark (q : unitInterval) (s : ℝ) (hs : 1 ≤ s) : unitInterval :=
  ⟨(q:ℝ)/s,div_nonneg q.2.1 (by linarith),
    (div_le_one (by linarith : 0 < s)).mpr (q.2.2.trans hs)⟩

theorem scaledMark_mul (q : unitInterval) (s : ℝ) (hs : 1 ≤ s) :
    (scaledMark q s hs:ℝ)*s=(q:ℝ) := div_mul_cancel₀ _ (by linarith)

theorem scaledMark_le (q : unitInterval) (s : ℝ) (hs : 1 ≤ s) :
    (scaledMark q s hs:ℝ) ≤ (q:ℝ) := by
  apply (div_le_iff₀ (by linarith : 0 < s)).mpr
  nlinarith [q.2.1]

theorem residualProbability_antitone_mark (p q q' : unitInterval)
    (hq : (q':ℝ) ≤ (q:ℝ)) (hpq : (p:ℝ)*(q:ℝ) < 1)
    (hpq' : (p:ℝ)*(q':ℝ) < 1) :
    (residualProbability p q hpq:ℝ) ≤ (residualProbability p q' hpq':ℝ) := by
  change (p:ℝ)*(1-(q:ℝ))/(1-(p:ℝ)*(q:ℝ)) ≤
    (p:ℝ)*(1-(q':ℝ))/(1-(p:ℝ)*(q':ℝ))
  apply (div_le_div_iff₀ (by linarith : 0 < 1-(p:ℝ)*(q:ℝ))
    (by linarith : 0 < 1-(p:ℝ)*(q':ℝ))).mpr
  have hh := mul_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)) (sub_nonneg.mpr hq)
  nlinarith

theorem witness_mark_tail_scaled {s cap mean : ℝ} (hs : 1 ≤ s) (hcap : 0 < cap) :
    exp (-(s*cap-s*mean)^2/(2*(s*cap))) ≤ exp (-(cap-mean)^2/(2*cap)) := by
  have hs0 : 0 < s := by linarith
  have he : -(s*cap-s*mean)^2/(2*(s*cap))=s*(-(cap-mean)^2/(2*cap)) := by
    field_simp <;> ring
  rw [he]
  apply exp_le_exp.mpr
  have hh : -(cap-mean)^2/(2*cap) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  nlinarith

def GlobalCutParameters.scale (C : GlobalCutParameters) (s : ℝ) : GlobalCutParameters where
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
  h := s*C.h
  t₀ := C.t₀
  κ := C.κ
  τ := C.τ

theorem GlobalCutParameters.valid_scale (C : GlobalCutParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ)) (hcap : 0 < C.cap) :
    (C.scale s).Valid p (scaledMark q s hs) ρ' (s^2*n) := by
  have hs0 : 0 < s := by linarith
  have hn : 0 < n := (mul_pos (by norm_num : (0:ℝ) < 9) hC.scale_pos).trans_le hC.order_scale
  have hqδ : (scaledMark q s hs:ℝ)*(s*C.δ)=(q:ℝ)*C.δ := by
    rw [← mul_assoc,scaledMark_mul]
  have hqu : (scaledMark q s hs:ℝ)*(s^2*C.upper)=s*((q:ℝ)*C.upper) := by
    change ((q:ℝ)/s)*(s^2*C.upper)=_
    field_simp <;> ring
  have herr : (2*(s*C.β)+(s*C.δ)*exp (-(scaledMark q s hs:ℝ)*(s*C.δ)))/(s*C.err)=
      (2*C.β+C.δ*exp (-(q:ℝ)*C.δ))/C.err := by
    rw [neg_mul, hqδ, ← neg_mul]
    field_simp <;> ring
  have htail : exp (-((s*C.cap)-(scaledMark q s hs:ℝ)*(s^2*C.upper))^2/(2*(s*C.cap))) ≤
      exp (-(C.cap-(q:ℝ)*C.upper)^2/(2*C.cap)) := by
    rw [hqu]
    exact witness_mark_tail_scaled hs hcap
  have hpop : C.slope*(p:ℝ)*C.c+(s*C.err)/(s*C.δ)+(s*C.b)/(s*C.δ-s*C.β)=
      C.slope*(p:ℝ)*C.c+C.err/C.δ+C.b/(C.δ-C.β) := by
    field_simp <;> ring
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
    order_scale := ?_
    side_scale_lower := hC.side_scale_lower
    side_scale_bound := ?_
    retained_nonneg := hC.retained_nonneg
    marked_retention := hC.marked_retention.trans hret
    fraction_nonneg := hC.fraction_nonneg
    fraction_le_one := hC.fraction_le_one
    cut_threshold := ?_ }
  · dsimp only [scale]
    change C.ω ≤ 1-(2*(s*C.β)+(s*C.δ)*exp (-(scaledMark q s hs:ℝ)*(s*C.δ)))/(s*C.err)-_
    rw [herr]
    linarith [hC.witness_bound]
  · change 9*(s*C.h) ≤ s^2*n
    have hh := mul_le_mul_of_nonneg_left hC.order_scale hs0.le
    have hh' : s*n ≤ s^2*n := mul_le_mul_of_nonneg_right (by nlinarith : s ≤ s^2) hn.le
    nlinarith
  · change C.t₀*(s*C.h) ≤ C.c*(s*C.δ-s*C.β)
    have hh := mul_le_mul_of_nonneg_left hC.side_scale_bound hs0.le
    nlinarith
  · change s*C.β+s*C.err ≤ C.τ*C.κ*(s*C.h)*C.c*(ρ':ℝ)^2
    have hh := mul_le_mul_of_nonneg_left hC.cut_threshold hs0.le
    have hr := pow_le_pow_left₀ ρ.2.1 hρ 2
    have hp := mul_le_mul_of_nonneg_left hr
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hs0.le hC.fraction_nonneg)
        hC.retained_nonneg) hC.scale_pos.le) hC.population_pos.le)
    nlinarith

end
end Cycle13
