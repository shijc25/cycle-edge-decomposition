import Cycle12.JansonDependencyUpper

namespace Cycle12
open Finset Cycle13 Real
noncomputable section

def jansonPhiPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, x^(k+2)/(((k:ℝ)+2)*((k:ℝ)+1))

theorem janson_phi_polynomial_derivative (n : ℕ) (x : ℝ) :
    HasDerivAt (jansonPhiPolynomial n)
      (∑ k ∈ range n, x^(k+1)/((k:ℝ)+1)) x := by
  have hh := HasDerivAt.fun_sum (u:=range n)
    (fun k _ => (hasDerivAt_pow (k+2) x).div_const (((k:ℝ)+2)*((k:ℝ)+1)))
  convert hh using 1
  · rfl
  · apply sum_congr rfl
    intro k _
    rw [show k+2-1=k+1 by omega]
    push_cast
    field_simp

theorem full_janson_phi_one_sub_derivative (x : ℝ) (hx : x<1) :
    HasDerivAt (fun y => fullJansonPhi (1-y)) (-log (1-x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1-y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hlog := h1.log (by linarith : 1-x≠0)
  have hh := (h1.const_sub 1).add (h1.mul hlog)
  convert hh using 1
  · rfl
  · field_simp [show 1-x≠0 by linarith] <;> ring

theorem full_janson_phi_continuous : Continuous fullJansonPhi := by
  exact (continuous_const.sub continuous_id).add continuous_mul_log

/-- A finite rational lower certificate for the full Janson rate. This
holds on the entire real interval, rather than only at grid points. -/
theorem janson_phi_polynomial_lower (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x<1) :
    jansonPhiPolynomial n x ≤ fullJansonPhi (1-x) := by
  let F : ℝ → ℝ := fun y => fullJansonPhi (1-y)-jansonPhiPolynomial n y
  have hD (y : ℝ) (hy : y<1) : HasDerivAt F
      (-log (1-y)-(∑ k ∈ range n, y^(k+1)/((k:ℝ)+1))) y :=
    (full_janson_phi_one_sub_derivative y hy).sub (janson_phi_polynomial_derivative n y)
  have hcont : Continuous F := by
    exact (full_janson_phi_continuous.comp (continuous_const.sub continuous_id)).sub
      (continuous_iff_continuousAt.mpr (fun y => (janson_phi_polynomial_derivative n y).continuousAt))
  have hmono : MonotoneOn F (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont.continuousOn
    · intro y hy
      exact (hD y ((interior_subset hy).2.trans_lt hx1)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy).1
      have hy1 : y<1 := (interior_subset hy).2.trans_lt hx1
      rw [(hD y hy1).deriv]
      have hh := hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hy0])
      have hn := sum_le_hasSum (range n) (fun k _ => div_nonneg (pow_nonneg hy0 _) (by positivity)) hh
      exact sub_nonneg.mpr (by simpa only [Nat.cast_add,Nat.cast_one] using hn)
  have hh := hmono (show 0∈Set.Icc (0:ℝ) x from ⟨le_refl _,hx0⟩)
    (show x∈Set.Icc (0:ℝ) x from ⟨hx0,le_refl _⟩) hx0
  have hzero : F 0=0 := by simp [F,fullJansonPhi,jansonPhiPolynomial]
  rw [hzero] at hh
  exact sub_nonneg.mp hh

theorem full_janson_phi_series_lower (n : ℕ) (tau : ℝ) (ht0 : 0<tau) (ht1 : tau≤1) :
    jansonPhiPolynomial n (1-tau) ≤ fullJansonPhi tau := by
  have hh := janson_phi_polynomial_lower n (1-tau) (by linarith) (by linarith)
  simpa only [sub_sub_cancel] using hh

/-- The verifier uses powers 2 through 16, i.e. 15 terms. -/
theorem full_janson_phi_sixteen_lower (tau : ℝ) (ht0 : 0<tau) (ht1 : tau≤1) :
    (∑ k ∈ range 15, (1-tau)^(k+2)/(((k:ℝ)+2)*((k:ℝ)+1))) ≤ fullJansonPhi tau :=
  full_janson_phi_series_lower 15 tau ht0 ht1

end
end Cycle12
