import Cycle12.Foundations.ScaledLocalSample

namespace Cycle13
open Real
noncomputable section

def normalizedMark (q z : ℝ) (hz : 0 < z) (hq : 0 ≤ q) (hqz : q ≤ z) : unitInterval :=
  ⟨q/z,div_nonneg hq hz.le,(div_le_one hz).mpr hqz⟩

def unnormalizedResidual (p q : unitInterval) : unitInterval :=
  ⟨(p:ℝ)*(1-(q:ℝ)),mul_nonneg p.2.1 (sub_nonneg.mpr q.2.2),
    (mul_le_mul_of_nonneg_left (by linarith [q.2.1] : 1-(q:ℝ) ≤ 1) p.2.1).trans (by simpa using p.2.2)⟩

theorem unnormalizedResidual_lower (p q : unitInterval) :
    (1-(p:ℝ)*(q:ℝ))*(unnormalizedResidual p q:ℝ) ≤ (p:ℝ)*(1-(q:ℝ)) := by
  change (1-(p:ℝ)*(q:ℝ))*((p:ℝ)*(1-(q:ℝ))) ≤ _
  have hh := mul_nonneg (mul_nonneg p.2.1 q.2.1) (mul_nonneg p.2.1 (sub_nonneg.mpr q.2.2))
  nlinarith

structure NormalizedGlobalParameters where
  dm : ℝ
  beta : ℝ
  err : ℝ
  upper : ℝ
  mark : ℝ
  cap : ℝ
  witness : ℝ
  slope : ℝ
  intercept : ℝ
  theta : ℝ
  population : ℝ
  retained : ℝ
  fraction : ℝ

namespace NormalizedGlobalParameters

def parameters (C : NormalizedGlobalParameters) (p z R : ℝ) : GlobalCutParameters where
  δ := C.dm*z
  β := C.beta*z
  err := C.err*z
  upper := C.upper*R*z
  cap := C.cap*R
  ω := C.witness
  slope := C.slope
  b := C.intercept*z
  θ := C.theta
  c := C.population/p
  h := z/p
  t₀ := C.population*(C.dm-C.beta)
  κ := C.retained
  τ := C.fraction

structure Valid (C : NormalizedGlobalParameters) (p z R : ℝ) : Prop where
  p_pos : 0 < p
  scale_pos : 0 < z
  ratio_lower : 9 ≤ R
  mark_nonneg : 0 ≤ C.mark
  mark_lt : C.mark < z
  degree_pos : 0 < C.dm
  expansion_lt : C.beta < C.dm
  error_pos : 0 < C.err
  mark_degree : 1 ≤ C.mark*C.dm
  cap_pos : 0 < C.cap
  mark_cap : C.upper*C.mark ≤ C.cap
  witness_pos : 0 < C.witness
  witness_bound : C.witness ≤ 1-(2*C.beta+C.dm*exp (-C.mark*C.dm))/C.err-
    exp (-R*(C.cap-C.upper*C.mark)^2/(2*C.cap))
  slope_pos : 0 < C.slope
  intercept_nonneg : 0 ≤ C.intercept
  theta_pos : 0 < C.theta
  mgf_slope : exp C.theta-1 ≤ C.theta*C.slope
  population_pos : 0 < C.population
  population_bound : C.slope*C.population+C.err/C.dm+C.intercept/(C.dm-C.beta) ≤ 1
  side_scale_lower : (107/100:ℝ) ≤ C.population*(C.dm-C.beta)
  retained_nonneg : 0 ≤ C.retained
  marked_retention : C.retained ≤ 1-1/R-C.cap*p*R/z
  fraction_nonneg : 0 ≤ C.fraction
  fraction_le_one : C.fraction ≤ 1
  cut_threshold : C.beta+C.err ≤ C.fraction*C.retained*C.population*(1-C.mark/z)^2

theorem valid (C : NormalizedGlobalParameters) {p : unitInterval} {z R : ℝ}
    (hC : C.Valid (p:ℝ) z R) :
    (C.parameters (p:ℝ) z R).Valid p
      (normalizedMark C.mark z hC.scale_pos hC.mark_nonneg hC.mark_lt.le)
      (unnormalizedResidual p (normalizedMark C.mark z hC.scale_pos hC.mark_nonneg hC.mark_lt.le))
      (R*z/(p:ℝ)) := by
  have hR : 0 < R := by linarith [hC.ratio_lower]
  have hz := hC.scale_pos
  have hp := hC.p_pos
  have hdm := hC.degree_pos
  have herr := hC.error_pos
  have hcap := hC.cap_pos
  have hmark : (C.mark/z)*(C.dm*z)=C.mark*C.dm := by field_simp
  have hmcap : (C.mark/z)*(C.upper*R*z)=R*(C.upper*C.mark) := by field_simp <;> ring
  have hw : (2*(C.beta*z)+(C.dm*z)*exp (-(C.mark/z)*(C.dm*z)))/(C.err*z)=
      (2*C.beta+C.dm*exp (-C.mark*C.dm))/C.err := by
    rw [neg_mul,hmark,← neg_mul]
    field_simp <;> ring
  have ht : -(C.cap*R-(C.mark/z)*(C.upper*R*z))^2/(2*(C.cap*R))=
      -R*(C.cap-C.upper*C.mark)^2/(2*C.cap) := by
    rw [hmcap]
    field_simp <;> ring
  have hpop : C.slope*(p:ℝ)*(C.population/(p:ℝ))+(C.err*z)/(C.dm*z)+
      (C.intercept*z)/(C.dm*z-C.beta*z)=
      C.slope*C.population+C.err/C.dm+C.intercept/(C.dm-C.beta) := by field_simp <;> ring
  have hret : 1-(z/(p:ℝ))/(R*z/(p:ℝ))-(C.cap*R)/(z/(p:ℝ))=
      1-1/R-C.cap*(p:ℝ)*R/z := by field_simp <;> ring
  refine {
    p_pos := hp
    residual_pos := mul_pos hp (sub_pos.mpr ((div_lt_one hz).mpr hC.mark_lt))
    degree_pos := mul_pos hdm hz
    cut_lt_degree := mul_lt_mul_of_pos_right hC.expansion_lt hz
    error_pos := mul_pos herr hz
    mark_degree := by simpa only [parameters,normalizedMark,hmark] using hC.mark_degree
    mark_cap := ?_
    witness_pos := hC.witness_pos
    witness_bound := ?_
    slope_pos := hC.slope_pos
    intercept_nonneg := mul_nonneg hC.intercept_nonneg hz.le
    theta_pos := hC.theta_pos
    mgf_slope := hC.mgf_slope
    population_pos := div_pos hC.population_pos hp
    population_bound := by simpa only [parameters,hpop] using hC.population_bound
    scale_pos := div_pos hz hp
    order_scale := ?_
    side_scale_lower := hC.side_scale_lower
    side_scale_bound := ?_
    retained_nonneg := hC.retained_nonneg
    marked_retention := by simpa only [parameters,hret] using hC.marked_retention
    fraction_nonneg := hC.fraction_nonneg
    fraction_le_one := hC.fraction_le_one
    cut_threshold := ?_ }
  · dsimp only [parameters,normalizedMark]
    rw [hmcap]
    nlinarith [mul_le_mul_of_nonneg_left hC.mark_cap hR.le]
  · dsimp only [parameters,normalizedMark]
    rw [hw,ht]
    exact hC.witness_bound
  · dsimp only [parameters]
    have hh := mul_le_mul_of_nonneg_right hC.ratio_lower (div_pos hz hp).le
    simpa only [mul_div_assoc] using hh
  · dsimp only [parameters]
    apply le_of_eq
    field_simp <;> ring
  · dsimp only [parameters,unnormalizedResidual,normalizedMark]
    have he : C.fraction*C.retained*(z/(p:ℝ))*(C.population/(p:ℝ))*
        ((p:ℝ)*(1-C.mark/z))^2=z*(C.fraction*C.retained*C.population*(1-C.mark/z)^2) := by
      field_simp <;> ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hC.cut_threshold hz.le]

def mgfRate (C : NormalizedGlobalParameters) (p z R : ℝ) : ℝ :=
  C.theta*C.intercept*(z/R)-C.mark*exp (C.theta*(1-C.slope*p))

def jansonRate (C : NormalizedGlobalParameters) (z R : ℝ) : ℝ :=
  (1-C.fraction)^2*(1-C.mark/z)*C.retained*(z/R)/
    (2*(2+1/((1-C.mark/z)*(C.population*(C.dm-C.beta))*z)))-C.mark

theorem failureBound_eq (C : NormalizedGlobalParameters) {p : unitInterval} {z R : ℝ}
    (hC : C.Valid (p:ℝ) z R) :
    (C.parameters (p:ℝ) z R).failureBound p
      (normalizedMark C.mark z hC.scale_pos hC.mark_nonneg hC.mark_lt.le)
      (unnormalizedResidual p (normalizedMark C.mark z hC.scale_pos hC.mark_nonneg hC.mark_lt.le))
      (R*z/(p:ℝ))=
      (2*exp (-R*C.mgfRate (p:ℝ) z R)+exp (-R*C.jansonRate z R))/C.witness := by
  have hR : 0 < R := by linarith [hC.ratio_lower]
  have hp := hC.p_pos
  have hz := hC.scale_pos
  unfold GlobalCutParameters.failureBound GlobalCutParameters.jansonRate parameters
    unnormalizedResidual normalizedMark mgfRate jansonRate
  congr 2
  · congr 2
    field_simp <;> ring
  · congr 1
    field_simp <;> ring

end NormalizedGlobalParameters
end
end Cycle13
