/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Foundations.FiniteLaw

/-! A finite-law lower-tail bound from a Laplace differential inequality.
The integration step uses a tilted exponential, avoiding division by the
Laplace transform. All hypotheses are explicit; the graph application must
separately establish the differential inequality. -/

namespace Cycle12.Independent
open Finset Real Cycle13
noncomputable section
variable {Ω : Type*} [Fintype Ω]

theorem finite_laplace_derivative (P : FiniteLaw Ω) (X : Ω → ℝ) (s : ℝ) :
    HasDerivAt (fun r => P.expect (fun ω => exp (-r * X ω)))
      (-P.expect (fun ω => X ω * exp (-s * X ω))) s := by
  have h : ∀ ω ∈ (univ : Finset Ω),
      HasDerivAt (fun r => P.mass ω * exp (-r * X ω))
        (P.mass ω * (exp (-s * X ω) * (-X ω))) s := by
    intro ω _
    convert (((hasDerivAt_id s).neg.mul_const (X ω)).exp.const_mul (P.mass ω)) using 1
    · funext r
      simp [mul_comm]
    · simp [mul_comm, mul_left_comm, mul_assoc]
  convert HasDerivAt.fun_sum h using 1
  · simp [FiniteLaw.expect]
  · simp only [FiniteLaw.expect, ← sum_neg_distrib]
    apply sum_congr rfl
    intro ω _
    ring

theorem finite_laplace_bound (P : FiniteLaw Ω) (X : Ω → ℝ) (μ v b : ℝ)
    (hb : 0 ≤ b)
    (hlocal : ∀ s ∈ Set.Icc 0 b,
      (μ-v*s) * P.expect (fun ω => exp (-s*X ω)) ≤
        P.expect (fun ω => X ω * exp (-s*X ω))) :
    P.expect (fun ω => exp (-b*X ω)) ≤ exp (-μ*b+v*b^2/2) := by
  let L (s : ℝ) := P.expect (fun ω => exp (-s*X ω))
  let H (s : ℝ) := exp (μ*s-v*s^2/2) * L s
  let H' (s : ℝ) := exp (μ*s-v*s^2/2) *
    ((μ-v*s)*L s - P.expect (fun ω => X ω * exp (-s*X ω)))
  have hH : ∀ s, HasDerivAt H (H' s) s := by
    intro s
    have hpoly : HasDerivAt (fun r : ℝ => μ*r-v*r^2/2) (μ-v*s) s := by
      convert ((hasDerivAt_id s).const_mul μ).sub
        ((((hasDerivAt_id s).pow 2).const_mul v).div_const 2) using 1
      · funext r
        simp
        <;> ring
      · simp
        <;> ring
    convert hpoly.exp.mul (finite_laplace_derivative P X s) using 1 <;> dsimp [H, H', L] <;> ring
  have hanti : AntitoneOn H (Set.Icc 0 b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 b)
      (fun s _ => (hH s).continuousAt.continuousWithinAt)
      (fun s _ => (hH s).hasDerivWithinAt)
      (fun s hs => mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
        (sub_nonpos.mpr (hlocal s (interior_subset hs))))
  have hbound := hanti (show (0:ℝ) ∈ Set.Icc 0 b from ⟨le_rfl, hb⟩)
    (show b ∈ Set.Icc 0 b from ⟨hb, le_rfl⟩) hb
  have hzero : H 0 = 1 := by simp [H, L]
  rw [hzero] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (exp_pos (-μ*b+v*b^2/2)).le
  simpa [H, L, ← mul_assoc, ← exp_add] using h

theorem finite_laplace_lower_tail (P : FiniteLaw Ω) (X : Ω → ℝ) {μ v t : ℝ}
    (hv : 0 < v) (ht0 : 0 ≤ t) (ht : t ≤ μ)
    (hlocal : ∀ s ∈ Set.Icc 0 (μ/v),
      (μ-v*s) * P.expect (fun ω => exp (-s*X ω)) ≤
        P.expect (fun ω => X ω * exp (-s*X ω))) :
    P.prob (fun ω => X ω ≤ μ-t) ≤ exp (-t^2/(2*v)) := by
  have hs : 0 ≤ t/v := div_nonneg ht0 hv.le
  have hsmall : t/v ≤ μ/v := div_le_div_of_nonneg_right ht hv.le
  have hmgf := finite_laplace_bound P X μ v (t/v) hs
    (fun s hs => hlocal s ⟨hs.1, hs.2.trans hsmall⟩)
  have hmarkov := P.exp_markov_le (fun ω => -X ω) (t/v) (t-μ) hs
  have hevent : (fun ω => t-μ ≤ -X ω) = (fun ω => X ω ≤ μ-t) := by
    funext ω
    apply propext
    constructor <;> intro h <;> linarith
  rw [hevent] at hmarkov
  have hexpect : P.expect (fun ω => exp (t/v * -X ω)) =
      P.expect (fun ω => exp (-(t/v)*X ω)) := by congr 1; funext ω; congr 1; ring
  rw [hexpect] at hmarkov
  refine hmarkov.trans ((mul_le_mul_of_nonneg_left hmgf (exp_pos _).le).trans_eq ?_)
  rw [← exp_add]
  congr 1
  field_simp
  ring

end
end Cycle12.Independent
