import Cycle12.LaplaceDifferential

namespace Cycle12
open Finset Cycle13 Real Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type} [Fintype Ω]

def fullJansonPhi (tau : ℝ) : ℝ := 1-tau+tau*log tau

theorem finite_laplace_markov (mu : FiniteLaw Ω) (X : Ω → ℝ) (s b : ℝ) (hs : 0 ≤ s) :
    mu.prob (fun x => X x ≤ b) ≤ exp (s*b)*finiteLaplace mu X s := by
  have hh := mu.exp_markov_le (fun x => -X x) s (-b) hs
  simpa only [neg_le_neg_iff,neg_mul_neg,mul_neg,neg_mul,neg_neg,finiteLaplace] using hh

theorem finite_lower_tail_of_laplace_pos (mu : FiniteLaw Ω) (X : Ω → ℝ)
    (m r : ℝ) (hr : 0 < r)
    (hL : ∀ s : ℝ, 0 ≤ s → finiteLaplace mu X s ≤ exp ((m/r)*(exp (-r*s)-1)))
    (tau : ℝ) (ht0 : 0 < tau) (ht1 : tau ≤ 1) :
    mu.prob (fun x => X x ≤ tau*m) ≤ exp (-(m/r)*fullJansonPhi tau) := by
  let s : ℝ := -log tau/r
  have hs : 0 ≤ s := div_nonneg (neg_nonneg.mpr (log_nonpos ht0.le ht1)) hr.le
  have hexp : exp (-r*s)=tau := by
    have he : -r*s=log tau := by dsimp only [s]; field_simp
    rw [he,exp_log ht0]
  calc
    _ ≤ exp (s*(tau*m))*finiteLaplace mu X s := finite_laplace_markov mu X s (tau*m) hs
    _ ≤ exp (s*(tau*m))*exp ((m/r)*(exp (-r*s)-1)) :=
      mul_le_mul_of_nonneg_left (hL s hs) (exp_pos _).le
    _ = _ := by
      rw [hexp,← exp_add]
      congr 1
      dsimp only [s,fullJansonPhi]
      ring

theorem finite_lower_tail_of_laplace_zero (mu : FiniteLaw Ω) (X : Ω → ℝ)
    (m r : ℝ) (hr : 0 < r)
    (hL : ∀ s : ℝ, 0 ≤ s → finiteLaplace mu X s ≤ exp ((m/r)*(exp (-r*s)-1))) :
    mu.prob (fun x => X x ≤ 0) ≤ exp (-(m/r)) := by
  have he : Tendsto (fun s : ℝ => exp (-r*s)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hr))
  have hl : Tendsto (fun s : ℝ => exp ((m/r)*(exp (-r*s)-1))) atTop (𝓝 (exp (-(m/r)))) := by
    simpa only [sub_eq_add_neg,zero_add,mul_neg,mul_one,Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp ((he.sub_const 1).const_mul (m/r))
  apply ge_of_tendsto hl
  filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
  have hm := finite_laplace_markov mu X s 0 hs
  simp only [mul_zero,exp_zero,one_mul] at hm
  exact hm.trans (hL s hs)

/-- The complete entropy-shaped lower tail, including tau=0 and tau=1. -/
theorem finite_lower_tail_of_laplace (mu : FiniteLaw Ω) (X : Ω → ℝ)
    (m r : ℝ) (hr : 0 < r)
    (hL : ∀ s : ℝ, 0 ≤ s → finiteLaplace mu X s ≤ exp ((m/r)*(exp (-r*s)-1)))
    (tau : ℝ) (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1) :
    mu.prob (fun x => X x ≤ tau*m) ≤ exp (-(m/r)*fullJansonPhi tau) := by
  rcases ht0.eq_or_lt with he | htpos
  · subst tau
    simpa only [fullJansonPhi,zero_mul,sub_zero,add_zero,mul_one] using
      finite_lower_tail_of_laplace_zero mu X m r hr hL
  · exact finite_lower_tail_of_laplace_pos mu X m r hr hL tau htpos ht1

end
end Cycle12
