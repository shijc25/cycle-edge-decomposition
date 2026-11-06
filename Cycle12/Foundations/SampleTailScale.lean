import Cycle12.Foundations.LocalSamplingScale

namespace Cycle13
open Real
noncomputable section

theorem exp_neg_scaled_le {s a : ℝ} (hs : 1 ≤ s) (ha : 0 ≤ a) :
    exp (-s*a) ≤ exp (-a) := exp_le_exp.mpr (by nlinarith)

theorem poissonRate_nonneg {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    0 ≤ poissonRate μ a := by
  have hh := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos (div_pos ha hμ)) ha.le
  have he : a*(1-(a/μ)⁻¹)=a-μ := by field_simp <;> ring
  rw [he] at hh
  unfold poissonRate
  linarith

theorem order_chernoff_scale {s μ a : ℝ} (hs : 1 ≤ s) (hμ : 0 < μ) (ha : 0 < a) :
    exp (-poissonRate (s^2*μ) (s^2*a)) ≤ exp (-poissonRate μ a) := by
  rw [poissonRate_scale (pow_ne_zero 2 (by linarith : s≠0))]
  simpa only [neg_mul] using exp_neg_scaled_le (s:=s^2) (by nlinarith) (poissonRate_nonneg hμ ha)

theorem GlobalCutParameters.failureBound_mono_scale (C : GlobalCutParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ))
    (hmgf : (p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n ≤ C.θ*C.b)
    (hJ : (p:ℝ)*(q:ℝ)*n ≤ C.jansonRate ρ) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤ C.failureBound p q ρ n := by
  apply (C.failureBound_scale hC hs hρ).trans
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply exp_le_exp.mpr
    nlinarith
  · apply exp_le_exp.mpr
    nlinarith

theorem AnchorParameters.failureBound_mono_scale (C : AnchorParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ))
    (hmgf : (p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n ≤ C.θ*C.b)
    (hJ : (p:ℝ)*(q:ℝ)*n ≤ C.jansonRate ρ) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤ C.failureBound p q ρ n := by
  apply (C.failureBound_scale hC hs hρ).trans
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply exp_le_exp.mpr
    nlinarith
  · apply exp_le_exp.mpr
    nlinarith

theorem LocalCutParameters.failureBound_mono_scale (C : LocalCutParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ)) (hell : 0 ≤ C.ell)
    (hmgf : (p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n ≤ C.θ*C.b)
    (hJ : (p:ℝ)*(q:ℝ)*n ≤ C.jansonRate ρ)
    (hrev : (p:ℝ)*(q:ℝ)*n ≤ (1-C.ν)^2*C.ell/2) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤ C.failureBound p q ρ n := by
  apply (C.failureBound_scale hC hs hρ hell).trans
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add
  · apply add_le_add <;> apply exp_le_exp.mpr <;> nlinarith
  · apply exp_le_exp.mpr
    nlinarith

def sampleVarianceScalar (p n m : ℝ) : ℝ := m*p^2+2*m*n*p^3*(1-p)

def sampleEdgeFailureScalar (p n m t : ℝ) : ℝ :=
  sampleVarianceScalar p n m/(sampleVarianceScalar p n m+t^2)

def incidentFailureScalar (p n m v : ℝ) : ℝ :=
  exp (-(m/n)*(v-2*p+p^2)^2/((1-p)*(4*p+2*(v-2*p+p^2)/3)))

theorem sampleVarianceScalar_nonneg {p n m : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    0 ≤ sampleVarianceScalar p n m := by
  unfold sampleVarianceScalar
  positivity

theorem sampleVarianceScalar_scale {p n m s : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hm : 0 ≤ m) (hs : 1 ≤ s) :
    sampleVarianceScalar p (s^2*n) (s^3*m) ≤ s^6*sampleVarianceScalar p n m := by
  have h₁ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs (show 3 ≤ 6 by decide))
    (mul_nonneg hm (sq_nonneg p))
  have h₂ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs (show 5 ≤ 6 by decide))
    (show 0 ≤ 2*m*n*p^3*(1-p) by positivity)
  unfold sampleVarianceScalar
  nlinarith

theorem sampleEdgeFailureScalar_scale {p n m t s : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (ht : 0 < t) (hs : 1 ≤ s) :
    sampleEdgeFailureScalar p (s^2*n) (s^3*m) (s^3*t) ≤ sampleEdgeFailureScalar p n m t := by
  have hs0 : 0 < s := by linarith
  have hv := sampleVarianceScalar_nonneg hp hp1 hn hm
  have hv' := sampleVarianceScalar_nonneg hp hp1
    (mul_nonneg (sq_nonneg s) hn) (mul_nonneg (pow_nonneg hs0.le 3) hm)
  have hh := sampleVarianceScalar_scale hp hp1 hn hm hs
  unfold sampleEdgeFailureScalar
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg t)
  nlinarith

theorem incidentFailureScalar_scale {p n m v s : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hn : 0 < n) (hm : 0 ≤ m)
    (hv : 2*p-p^2 < v) (hs : 1 ≤ s) :
    incidentFailureScalar p (s^2*n) (s^3*m) v ≤ incidentFailureScalar p n m v := by
  have hs0 : 0 < s := by linarith
  have hden : 0 < (1-p)*(4*p+2*(v-2*p+p^2)/3) :=
    mul_pos (by linarith) (by linarith)
  have he : -((s^3*m)/(s^2*n))*(v-2*p+p^2)^2/((1-p)*(4*p+2*(v-2*p+p^2)/3))=
      -s*((m/n)*(v-2*p+p^2)^2/((1-p)*(4*p+2*(v-2*p+p^2)/3))) := by
    field_simp <;> ring
  unfold incidentFailureScalar
  rw [he]
  have hb : 0 ≤ (m/n)*(v-2*p+p^2)^2/((1-p)*(4*p+2*(v-2*p+p^2)/3)) :=
    div_nonneg (mul_nonneg (div_nonneg hm hn.le) (sq_nonneg _)) hden.le
  have hh := exp_neg_scaled_le hs hb
  convert hh using 1 <;> congr 1 <;> ring

end
end Cycle13
