import Cycle12.HypergeometricRootGeometry

namespace Cycle12
open Polynomial Finset
noncomputable section

def hypergeomPolynomial (d b t : ℕ) : Polynomial ℂ :=
  ∑ j∈range (t+1), C ((d.choose j:ℂ)*(b.choose (t-j):ℂ))*X^j

theorem hypergeom_polynomial_eval (d b t : ℕ) (z : ℂ) :
    (hypergeomPolynomial d b t).eval z=
      ∑ j∈range (t+1), (d.choose j:ℂ)*(b.choose (t-j):ℂ)*z^j := by
  simp only [hypergeomPolynomial,eval_finset_sum,eval_mul,eval_C,eval_pow,eval_X]

theorem hypergeom_polynomial_eval_one (d b t : ℕ) :
    (hypergeomPolynomial d b t).eval 1=((d+b).choose t:ℂ) := by
  rw [hypergeom_polynomial_eval]
  simp only [one_pow,mul_one]
  have hh := Nat.add_choose_eq d b t
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  exact_mod_cast hh.symm

theorem descending_power_ratio (d k : ℕ) {x : ℂ} (hx : x≠0) :
    (d.descFactorial k:ℂ)*x^(d-k)=(d.descFactorial k:ℂ)*x^d/x^k := by
  by_cases hk : k ≤ d
  · rw [pow_sub₀ x hx hk]
    ring
  · have he : d.descFactorial k=0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp only [he,Nat.cast_zero,zero_mul,zero_div]

theorem derivative_X_power_eval_ratio (d k : ℕ) {x : ℂ} (hx : x≠0) :
    (derivative^[k] ((X:Polynomial ℂ)^d)).eval x=(d.descFactorial k:ℂ)*x^d/x^k := by
  rw [iterate_derivative_X_pow_eq_C_mul]
  simp only [eval_mul,eval_C,eval_pow,eval_X]
  exact descending_power_ratio d k hx

theorem derivative_X_add_one_eval_ratio (b k : ℕ) {x : ℂ} (hx : x+1≠0) :
    (derivative^[k] ((X+1:Polynomial ℂ)^b)).eval x=
      (b.descFactorial k:ℂ)*(x+1)^b/(x+1)^k := by
  have hh := iterate_derivative_X_add_pow (R:=ℂ) b k 1
  simp only [map_one,nsmul_eq_mul] at hh
  rw [hh]
  simp only [eval_mul,eval_natCast,eval_pow,eval_add,eval_X,eval_one]
  exact descending_power_ratio b k hx

theorem rodrigues_coefficient_identity (d b t j : ℕ) (hj : j ≤ t) :
    t.choose j*b.descFactorial (t-j)*d.descFactorial j=
      t.factorial*d.choose j*b.choose (t-j) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.descFactorial_eq_factorial_mul_choose]
  calc
    _ = (t.choose j*j.factorial*(t-j).factorial)*(d.choose j*b.choose (t-j)) := by ring
    _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial hj]; ring

/-- Rodrigues identity with rational factors; nonzero x and x+1 make it
valid uniformly, even when the derivative order exceeds either original exponent. -/
theorem hypergeom_rodrigues_eval (d b t : ℕ) {x : ℂ} (hx : x≠0) (hx1 : x+1≠0) :
    (derivative^[t] ((X:Polynomial ℂ)^d*(X+1)^b)).eval x=
      (t.factorial:ℂ)*x^d*(x+1)^b/(x+1)^t*
        (hypergeomPolynomial d b t).eval ((x+1)/x) := by
  rw [mul_comm ((X:Polynomial ℂ)^d),iterate_derivative_mul]
  simp only [eval_finset_sum,nsmul_eq_mul,eval_mul,eval_natCast]
  rw [hypergeom_polynomial_eval,mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjt : j ≤ t := by simpa only [mem_range,Nat.lt_succ_iff] using hj
  rw [derivative_X_add_one_eval_ratio b (t-j) hx1,derivative_X_power_eval_ratio d j hx]
  have hc : (t.choose j:ℂ)*(b.descFactorial (t-j):ℂ)*(d.descFactorial j:ℂ)=
      (t.factorial:ℂ)*(d.choose j:ℂ)*(b.choose (t-j):ℂ) := by
    exact_mod_cast rodrigues_coefficient_identity d b t j hjt
  calc
    _ = ((t.choose j:ℂ)*(b.descFactorial (t-j):ℂ)*(d.descFactorial j:ℂ))*
        (x^d*(x+1)^b/(x^j*(x+1)^(t-j))) := by ring
    _ = ((t.factorial:ℂ)*(d.choose j:ℂ)*(b.choose (t-j):ℂ))*
        (x^d*(x+1)^b/(x^j*(x+1)^(t-j))) := by rw [hc]
    _ = _ := by
      rw [pow_sub₀ (x+1) hx1 hjt,div_pow]
      field_simp
      <;> ring

end
end Cycle12
