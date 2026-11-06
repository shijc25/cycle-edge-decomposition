import Cycle12.MajorityEnvelopeTransfer
import Cycle12.Foundations.RationalBounds

namespace Cycle12
open Finset Real Cycle13

theorem rat_exp_partial_lower {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (ratExpPartial x n:ℝ) ≤ exp (x:ℝ) := by
  rw [cast_ratExpPartial]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) n

/-- A rational reciprocal of a positive Taylor lower bound proves a
negative exponential upper bound, including deliberate exponent rounding. -/
theorem rational_negative_exp_upper {q x r : ℚ} (n : ℕ)
    (hx : 0 ≤ x) (hqx : 2*x ≤ q) (hr : 0 ≤ r)
    (hpartial : 1 ≤ r*ratExpPartial x n) : exp (-(q:ℝ)) ≤ (r:ℝ)^2 := by
  have hrR : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hprod : (1:ℝ) ≤ (r:ℝ)*exp (x:ℝ) := by
    have hh : (1:ℝ) ≤ (r:ℝ)*(ratExpPartial x n:ℝ) := by exact_mod_cast hpartial
    exact hh.trans (mul_le_mul_of_nonneg_left (rat_exp_partial_lower hx n) hrR)
  have hrec : exp (-(x:ℝ)) ≤ (r:ℝ) := by
    rw [exp_neg,inv_le_iff_one_le_mul₀ (exp_pos _)]
    exact hprod
  calc
    _ ≤ exp (-2*(x:ℝ)) := exp_le_exp.mpr (by
      have hh : (2:ℝ)*(x:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqx
      linarith only [hh])
    _ = exp (-(x:ℝ))^2 := by rw [← exp_nat_mul]; congr 1; ring
    _ ≤ (r:ℝ)^2 := pow_le_pow_left₀ (exp_pos _).le hrec 2

theorem rational_poisson_two_upper {q x r a : ℚ} (n : ℕ)
    (hx : 0 ≤ x) (hqx : 2*x ≤ q) (hr : 0 ≤ r)
    (hpartial : 1 ≤ r*ratExpPartial x n)
    (hbound : min 1 (r^2*(1+q+q^2/2)) ≤ a) : min 1 (poissonTailTwo (q:ℝ)) ≤ (a:ℝ) := by
  have hh := rational_negative_exp_upper n hx hqx hr hpartial
  have hf : (0:ℝ) ≤ 1+(q:ℝ)+(q:ℝ)^2/2 := by nlinarith [sq_nonneg ((q:ℝ)+1)]
  have hp := mul_le_mul_of_nonneg_right hh hf
  have hmin := min_le_min_left (1:ℝ) hp
  unfold poissonTailTwo
  apply hmin.trans
  have hc := (Rat.cast_le (K:=ℝ)).mpr hbound
  norm_num only [Rat.cast_min,Rat.cast_one,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,
    Rat.cast_div,Rat.cast_ofNat] at hc
  exact hc

end Cycle12
