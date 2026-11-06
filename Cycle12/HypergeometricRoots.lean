import Cycle12.HypergeometricRodrigues

namespace Cycle12
open Polynomial Finset
noncomputable section

/-- Every complex root of the hypergeometric generating polynomial is
real and nonpositive. Endpoint roots are treated separately, so the
Möbius transformation never divides by zero. -/
theorem hypergeom_polynomial_roots_real_nonpositive (d b t : ℕ) (ht : t ≤ d+b)
    {z : ℂ} (hz : (hypergeomPolynomial d b t).IsRoot z) : z.im=0 ∧ z.re ≤ 0 := by
  by_cases hz0 : z=0
  · subst z
    norm_num
  have hz1 : z≠1 := by
    intro he
    subst z
    have hh := hypergeom_polynomial_eval_one d b t
    have hn : ((d+b).choose t:ℂ)≠0 := by exact_mod_cast (Nat.choose_pos ht).ne'
    exact hn (hh.symm.trans hz)
  let x : ℂ := 1/(z-1)
  have hzm : z-1≠0 := sub_ne_zero.mpr hz1
  have hx : x≠0 := one_div_ne_zero hzm
  have hmul : x*(z-1)=1 := by dsimp [x]; field_simp
  have hsum : (x+1)*(z-1)=z := by linear_combination hmul
  have hx1 : x+1≠0 := by
    intro h
    rw [h,zero_mul] at hsum
    exact hz0 hsum.symm
  have hmobius : (x+1)/x=z := by
    apply (div_eq_iff hx).mpr
    linear_combination -hmul
  have hderiv : (derivative^[t] ((X:Polynomial ℂ)^d*(X+1)^b)).IsRoot x := by
    change (derivative^[t] ((X:Polynomial ℂ)^d*(X+1)^b)).eval x=0
    rw [hypergeom_rodrigues_eval d b t hx hx1,hmobius,hz,mul_zero]
  obtain ⟨hxi,hxl,hxu⟩ := binomial_derivative_roots_in_segment d b t ht x hderiv
  have hreal : x=(x.re:ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hxi
  have hzreal : z=(((x.re+1)/x.re:ℝ):ℂ) := by
    rw [← hmobius,hreal]
    push_cast
    rfl
  rw [hzreal]
  simp only [Complex.ofReal_im,Complex.ofReal_re,true_and]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith only [hxl]) hxu

theorem hypergeom_polynomial_ne_zero (d b t : ℕ) (ht : t ≤ d+b) :
    hypergeomPolynomial d b t≠0 := by
  intro he
  have hh := hypergeom_polynomial_eval_one d b t
  rw [he,eval_zero] at hh
  have hn : ((d+b).choose t:ℂ)≠0 := by exact_mod_cast (Nat.choose_pos ht).ne'
  exact hn hh.symm

end
end Cycle12
