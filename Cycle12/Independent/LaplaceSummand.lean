/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Independent.LaplaceTail

/-! A single-indicator estimate for the lower-tail differential inequality. -/
namespace Cycle12.Independent
open Real Finset Cycle13
noncomputable section
variable {Ω : Type*} [Fintype Ω]

theorem laplace_indicator_summand (P : FiniteLaw Ω) (I Y Z X : Ω → ℝ)
    {q r s : ℝ} (hs : 0 ≤ s) (hqr : 0 ≤ q-s*r)
    (hI : ∀ ω, I ω = 0 ∨ I ω = 1)
    (hY : ∀ ω, 0 ≤ Y ω)
    (hX : ∀ ω, X ω = I ω + Y ω + Z ω)
    (hind : P.expect (fun ω => I ω * exp (-s*Z ω)) =
      q * P.expect (fun ω => exp (-s*Z ω)))
    (hdep : P.expect (fun ω => I ω * Y ω * exp (-s*Z ω)) ≤
      r * P.expect (fun ω => exp (-s*Z ω))) :
    exp (-s) * (q-s*r) * P.expect (fun ω => exp (-s*X ω)) ≤
      P.expect (fun ω => I ω * exp (-s*X ω)) := by
  have hpoint : ∀ ω,
      exp (-s) * (I ω * exp (-s*Z ω) - s*(I ω*Y ω*exp (-s*Z ω))) ≤
        I ω * exp (-s*X ω) := by
    intro ω
    rcases hI ω with hzero | hone
    · simp [hzero]
    · rw [hone, one_mul, one_mul, one_mul, hX ω, hone]
      have he := Real.add_one_le_exp (-s*Y ω)
      have hm := mul_le_mul_of_nonneg_left he
        (mul_nonneg (exp_pos (-s)).le (exp_pos (-s*Z ω)).le)
      have hex : exp (-s) * exp (-s*Z ω) * exp (-s*Y ω) =
          exp (-s*(1+Y ω+Z ω)) := by
        rw [← exp_add, ← exp_add]
        congr 1
        ring
      rw [hex] at hm
      nlinarith
  have he := P.expect_mono hpoint
  have hexpand : P.expect (fun ω =>
      exp (-s) * (I ω * exp (-s*Z ω) - s*(I ω*Y ω*exp (-s*Z ω)))) =
      exp (-s) * (P.expect (fun ω => I ω * exp (-s*Z ω)) -
        s * P.expect (fun ω => I ω * Y ω * exp (-s*Z ω))) := by
    simp only [FiniteLaw.expect, mul_sub, sum_sub_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro ω _ <;> ring
  rw [hexpand, hind] at he
  have hZ : P.expect (fun ω => exp (-s*X ω)) ≤ P.expect (fun ω => exp (-s*Z ω)) := by
    apply P.expect_mono
    intro ω
    apply exp_le_exp.mpr
    have hI0 : 0 ≤ I ω := by rcases hI ω with h | h <;> simp [h]
    have hZX : Z ω ≤ X ω := by rw [hX ω]; linarith [hY ω]
    exact mul_le_mul_of_nonpos_left hZX (neg_nonpos.mpr hs)
  have hdep' := mul_le_mul_of_nonneg_left hdep hs
  have hcoef := mul_le_mul_of_nonneg_left hZ (mul_nonneg (exp_pos (-s)).le hqr)
  have hstep : exp (-s)*(q-s*r)*P.expect (fun ω => exp (-s*Z ω)) ≤
      exp (-s)*(q*P.expect (fun ω => exp (-s*Z ω)) -
        s*P.expect (fun ω => I ω*Y ω*exp (-s*Z ω))) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (exp_pos (-s)).le
    nlinarith
  exact hcoef.trans (hstep.trans he)

end
end Cycle12.Independent
