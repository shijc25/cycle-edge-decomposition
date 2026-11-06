import Cycle12.Foundations.FiniteLaw

/-! One-sided second-moment bounds for a finite probability law. -/
namespace Cycle13.FiniteLaw
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem expect_sub (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω-Y ω)=μ.expect X-μ.expect Y := by
  simp only [expect,mul_sub,sum_sub_distrib]

theorem markov_mul (μ : FiniteLaw Ω) (X : Ω → ℝ) (hX : ∀ ω, 0≤X ω) (t : ℝ) :
    t*μ.prob (fun ω => t ≤ X ω) ≤ μ.expect X := by
  rw [prob,← expect_const_mul]
  apply μ.expect_mono
  intro ω
  by_cases h : t ≤ X ω
  · simpa only [if_pos h,mul_one] using h
  · simpa only [if_neg h,mul_zero] using hX ω

theorem expect_centered_shift_sq (μ : FiniteLaw Ω) (X : Ω → ℝ) (m c : ℝ)
    (hmean : μ.expect X=m) :
    μ.expect (fun ω => (m-X ω+c)^2)=μ.expect (fun ω => (X ω-m)^2)+c^2 := by
  have he : (fun ω => (m-X ω+c)^2)=
      (fun ω => (X ω-m)^2+(-2*c)*(X ω-m)+c^2) := by funext ω; ring
  rw [he,expect_add,expect_add,expect_const_mul,expect_sub,hmean,expect_const,
    sub_self,mul_zero,add_zero,expect_const]

theorem cantelli_shift (μ : FiniteLaw Ω) (X : Ω → ℝ) {m v t c : ℝ}
    (hmean : μ.expect X=m) (hvar : μ.expect (fun ω => (X ω-m)^2) ≤ v)
    (ht : 0<t) (hc : 0≤c) :
    μ.prob (fun ω => X ω ≤ m-t) ≤ (v+c^2)/(t+c)^2 := by
  have htc : 0<(t+c)^2 := sq_pos_of_pos (by linarith)
  apply (le_div_iff₀ htc).mpr
  have hevent : ∀ ω, X ω ≤ m-t → (t+c)^2 ≤ (m-X ω+c)^2 := by
    intro ω hω
    have hh : t+c ≤ m-X ω+c := by linarith
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (μ.prob_mono hevent) htc.le
  have hm := μ.markov_mul (fun ω => (m-X ω+c)^2) (fun ω => sq_nonneg _) ((t+c)^2)
  rw [expect_centered_shift_sq μ X m c hmean] at hm
  nlinarith

theorem cantelli_lower (μ : FiniteLaw Ω) (X : Ω → ℝ) {m v t : ℝ}
    (hmean : μ.expect X=m) (hvar : μ.expect (fun ω => (X ω-m)^2) ≤ v)
    (ht : 0<t) :
    μ.prob (fun ω => X ω ≤ m-t) ≤ v/(v+t^2) := by
  have hv : 0≤v := (μ.expect_nonneg (fun ω => sq_nonneg _)).trans hvar
  have hb := cantelli_shift μ X hmean hvar ht (div_nonneg hv ht.le)
  apply hb.trans_eq
  have hden : 0<v+t^2 := add_pos_of_nonneg_of_pos hv (sq_pos_of_pos ht)
  have hshift : 0<t+v/t := add_pos_of_pos_of_nonneg ht (div_nonneg hv ht.le)
  field_simp [ht.ne',hden.ne',hshift.ne']
  <;> ring

end
end Cycle13.FiniteLaw
