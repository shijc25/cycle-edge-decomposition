import Mathlib

namespace Cycle12
open Polynomial Set
noncomputable section

def realRootSegment : Set ℂ := {z | z.im=0 ∧ -1 ≤ z.re ∧ z.re ≤ 0}

theorem real_root_segment_convex : Convex ℝ realRootSegment := by
  intro x hx y hy a b ha hb hab
  change (a • x+b • y).im=0 ∧ -1 ≤ (a • x+b • y).re ∧ (a • x+b • y).re ≤ 0
  simp only [Complex.add_im,Complex.add_re,Complex.smul_im,Complex.smul_re,smul_eq_mul]
  obtain ⟨hxi,hxl,hxu⟩ := hx
  obtain ⟨hyi,hyl,hyu⟩ := hy
  refine ⟨by rw [hxi,hyi]; ring,?_,?_⟩
  · have h₁ := mul_le_mul_of_nonneg_left hxl ha
    have h₂ := mul_le_mul_of_nonneg_left hyl hb
    nlinarith only [h₁,h₂,hab]
  · exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxu)
      (mul_nonpos_of_nonneg_of_nonpos hb hyu)

/-- Gauss-Lucas keeps every derivative root on the real segment [-1,0].
The nonconstant-degree hypothesis explicitly excludes the zero derivative. -/
theorem segment_roots_derivative (P : Polynomial ℂ)
    (hP : ∀ z, P.IsRoot z → z∈realRootSegment) (hdeg : 0<P.natDegree) :
    ∀ z, P.derivative.IsRoot z → z∈realRootSegment := by
  intro z hz
  have hn : P.derivative≠0 := derivative_ne_zero.mpr hdeg.ne'
  have hzset : z∈P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet,Polynomial.coe_aeval_eq_eval]
    exact ⟨hn,hz⟩
  have hsub : P.rootSet ℂ⊆realRootSegment := by
    intro w hw
    rw [Polynomial.mem_rootSet,Polynomial.coe_aeval_eq_eval] at hw
    exact hP w hw.2
  exact (convexHull_min hsub real_root_segment_convex)
    (P.rootSet_derivative_subset_convexHull_rootSet
      (natDegree_pos_iff_degree_pos.mp hdeg) hzset)

theorem iterated_derivative_natDegree_complex (P : Polynomial ℂ) (t : ℕ) :
    (derivative^[t] P).natDegree=P.natDegree-t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega

theorem segment_roots_iterated_derivative (P : Polynomial ℂ)
    (hP : ∀ z, P.IsRoot z → z∈realRootSegment) {t : ℕ} (ht : t ≤ P.natDegree) :
    ∀ z, (derivative^[t] P).IsRoot z → z∈realRootSegment := by
  induction t with
  | zero => simpa only [Function.iterate_zero,Function.id_def] using hP
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    apply segment_roots_derivative _ (ih (by omega))
    rw [iterated_derivative_natDegree_complex]
    omega

theorem binomial_root_polynomial_degree (d b : ℕ) :
    ((X:Polynomial ℂ)^d*(X+1)^b).natDegree=d+b := by
  have h₁ : (X:Polynomial ℂ)≠0 := X_ne_zero
  have h₂ : (X+1:Polynomial ℂ)≠0 := by simpa using (X_add_C_ne_zero (1:ℂ))
  rw [natDegree_mul (pow_ne_zero _ h₁) (pow_ne_zero _ h₂),natDegree_pow,natDegree_pow]
  have hh : (X+1:Polynomial ℂ).natDegree=1 := by simpa using natDegree_X_add_C (1:ℂ)
  simp only [hh,natDegree_X,mul_one]

/-- The real-root geometry underlying the hypergeometric generating
polynomial. This covers every derivative order used in its Rodrigues formula. -/
theorem binomial_derivative_roots_in_segment (d b t : ℕ) (ht : t ≤ d+b) :
    ∀ z : ℂ, (derivative^[t] ((X:Polynomial ℂ)^d*(X+1)^b)).IsRoot z →
      z.im=0 ∧ -1 ≤ z.re ∧ z.re ≤ 0 := by
  apply segment_roots_iterated_derivative
  · intro z hz
    change (eval z ((X:Polynomial ℂ)^d*(X+1)^b))=0 at hz
    simp only [eval_mul,eval_pow,eval_X,eval_add,eval_one] at hz
    rcases mul_eq_zero.mp hz with h | h
    · have hz0 : z=0 := eq_zero_of_pow_eq_zero h
      subst z
      norm_num [realRootSegment]
    · have hz1 : z+1=0 := eq_zero_of_pow_eq_zero h
      have hzneg : z = -1 := eq_neg_of_add_eq_zero_left hz1
      subst z
      norm_num [realRootSegment]
  · simpa only [binomial_root_polynomial_degree] using ht

end
end Cycle12
