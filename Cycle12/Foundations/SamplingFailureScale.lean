import Cycle12.Foundations.AnchorScale
import Cycle12.Foundations.ScaleTailBounds

namespace Cycle13
open Real
noncomputable section

theorem janson_kernel_scale {c u x x' s : ℝ}
    (hc : 0 ≤ c) (hu : 0 < u) (hx : 0 < x) (hs : 1 ≤ s) (hxx : s*x ≤ x') :
    s*(c*x/(2*(2+1/(u*x)))) ≤ c*x'/(2*(2+1/(u*x'))) := by
  have hs0 : 0 ≤ s := by linarith
  have hxx' : x ≤ x' := by nlinarith
  have hx' : 0 < x' := hx.trans_le hxx'
  have hden := one_div_le_one_div_of_le (mul_pos hu hx) (mul_le_mul_of_nonneg_left hxx' hu.le)
  have hnum : s*(c*x) ≤ c*x' := by nlinarith [mul_le_mul_of_nonneg_left hxx hc]
  calc
    _ = (s*(c*x))/(2*(2+1/(u*x))) := (mul_div_assoc ..).symm
    _ ≤ (c*x')/(2*(2+1/(u*x))) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hc hx'.le) (by positivity) (by linarith)

theorem GlobalCutParameters.jansonRate_scale (C : GlobalCutParameters)
    {ρ ρ' : unitInterval} {s : ℝ} (hs : 1 ≤ s) (hρ : 0 < (ρ:ℝ))
    (hρ' : (ρ:ℝ) ≤ (ρ':ℝ)) (hκ : 0 ≤ C.κ) (hh : 0 < C.h) (ht : 0 < C.t₀) :
    s*C.jansonRate ρ ≤ (C.scale s).jansonRate ρ' := by
  have hb : s*(C.h*(ρ:ℝ)) ≤ (s*C.h)*(ρ':ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hρ' (mul_nonneg (by linarith : 0 ≤ s) hh.le)
    nlinarith
  have hk := janson_kernel_scale (mul_nonneg (sq_nonneg (1-C.τ)) hκ) ht (mul_pos hh hρ) hs hb
  unfold jansonRate scale
  convert hk using 1 <;> ring

theorem AnchorParameters.jansonRate_scale (C : AnchorParameters)
    {ρ ρ' : unitInterval} {s : ℝ} (hs : 1 ≤ s) (hρ : 0 < (ρ:ℝ))
    (hρ' : (ρ:ℝ) ≤ (ρ':ℝ)) (hκ : 0 ≤ C.κ) (hh : 0 < C.h) (ht : 0 < C.t₀) :
    s*C.jansonRate ρ ≤ (C.scale s).jansonRate ρ' := by
  have hb : s*(C.h*(ρ:ℝ)) ≤ (s*C.h)*(ρ':ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hρ' (mul_nonneg (by linarith : 0 ≤ s) hh.le)
    nlinarith
  have hk := janson_kernel_scale (mul_nonneg (sq_nonneg (1-C.τ)) hκ) ht (mul_pos hh hρ) hs hb
  unfold jansonRate scale
  convert hk using 1 <;> ring

theorem GlobalCutParameters.failureBound_scale (C : GlobalCutParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ)) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤
      (2*exp (s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n))+
        exp (s*(-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n)))/C.ω := by
  have hs0 : 0 < s := by linarith
  have hJ := C.jansonRate_scale hs hC.residual_pos hρ hC.retained_nonneg hC.scale_pos
    (by linarith [hC.side_scale_lower] : 0 < C.t₀)
  have hmgf : -(C.scale s).θ*(C.scale s).b+(p:ℝ)*(scaledMark q s hs:ℝ)*
      exp ((C.scale s).θ*(1-(C.scale s).slope*(p:ℝ)))*(s^2*n)=
      s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n) := by
    dsimp only [scale,scaledMark]
    field_simp <;> ring
  have hent : (p:ℝ)*(scaledMark q s hs:ℝ)*(s^2*n)=s*((p:ℝ)*(q:ℝ)*n) := by
    dsimp only [scaledMark]
    field_simp <;> ring
  unfold failureBound
  rw [hmgf,hent]
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add le_rfl
  exact exp_le_exp.mpr (by linarith)

theorem AnchorParameters.failureBound_scale (C : AnchorParameters)
    {p q ρ ρ' : unitInterval} {n s : ℝ}
    (hC : C.Valid p q ρ n) (hs : 1 ≤ s) (hρ : (ρ:ℝ) ≤ (ρ':ℝ)) :
    (C.scale s).failureBound p (scaledMark q s hs) ρ' (s^2*n) ≤
      (2*exp (s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n))+
        exp (s*(-C.jansonRate ρ+(p:ℝ)*(q:ℝ)*n)))/C.ω := by
  have hs0 : 0 < s := by linarith
  have hJ := C.jansonRate_scale hs hC.residual_pos hρ hC.retained_nonneg hC.scale_pos
    (by linarith [hC.side_scale_lower] : 0 < C.t₀)
  have hmgf : -(C.scale s).θ*(C.scale s).b+(p:ℝ)*(scaledMark q s hs:ℝ)*
      exp ((C.scale s).θ*(1-(C.scale s).slope*(p:ℝ)))*(s^2*n)=
      s*(-C.θ*C.b+(p:ℝ)*(q:ℝ)*exp (C.θ*(1-C.slope*(p:ℝ)))*n) := by
    dsimp only [scale,scaledMark]
    field_simp <;> ring
  have hent : (p:ℝ)*(scaledMark q s hs:ℝ)*(s^2*n)=s*((p:ℝ)*(q:ℝ)*n) := by
    dsimp only [scaledMark]
    field_simp <;> ring
  unfold failureBound
  rw [hmgf,hent]
  apply div_le_div_of_nonneg_right _ hC.witness_pos.le
  apply add_le_add le_rfl
  exact exp_le_exp.mpr (by linarith)

theorem poissonRate_scale {s μ a : ℝ} (hs : s≠0) :
    poissonRate (s*μ) (s*a)=s*poissonRate μ a := by
  unfold poissonRate
  rw [mul_div_mul_left _ _ hs]
  ring

theorem degree_chernoff_scale {s n μ a : ℝ}
    (hs : 1 ≤ s) (hn : 0 ≤ n) (hrate : 2 ≤ poissonRate μ a) :
    (s^2*n)*exp (-poissonRate (s*μ) (s*a)) ≤ n*exp (-poissonRate μ a) := by
  rw [poissonRate_scale (by linarith : s≠0)]
  have hh := mul_le_mul_of_nonneg_left (polynomial_exp_tail_scale hs (k:=2) hrate) hn
  convert hh using 1 <;> ring

end
end Cycle13
