import Cycle12.BernoulliToFixedTransfer

namespace Cycle12
open Finset Polynomial Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

def binomialCDFPolynomial (n k : ℕ) : Polynomial ℝ :=
  ∑ j∈range (k+1), bernsteinPolynomial ℝ n j

theorem binomial_cdf_polynomial_derivative (n k : ℕ) :
    derivative (binomialCDFPolynomial n k)=-(n:Polynomial ℝ)*bernsteinPolynomial ℝ (n-1) k := by
  induction k with
  | zero => simp only [binomialCDFPolynomial,Nat.zero_add,sum_range_one,bernsteinPolynomial.derivative_zero]
  | succ k ih =>
    have he : binomialCDFPolynomial n (k+1)=
        binomialCDFPolynomial n k+bernsteinPolynomial ℝ n (k+1) := by
      exact sum_range_succ _ _
    rw [he,derivative_add,ih,bernsteinPolynomial.derivative_succ]
    ring

theorem binomial_cdf_derivative (n k : ℕ) (x : ℝ) :
    HasDerivAt (binomialCDFPolynomial n k).eval
      (-(n:ℝ)*(bernsteinPolynomial ℝ (n-1) k).eval x) x := by
  have hh := (binomialCDFPolynomial n k).hasDerivAt x
  simpa only [binomial_cdf_polynomial_derivative,eval_mul,eval_neg,eval_natCast] using hh

theorem bernstein_real_eval (n k : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℝ n k).eval x=(n.choose k:ℝ)*x^k*(1-x)^(n-k) := by
  simp only [bernsteinPolynomial,eval_mul,eval_pow,eval_natCast,eval_X,eval_sub,eval_one]

theorem binomial_cdf_nonneg (n k : ℕ) (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) :
    0≤(binomialCDFPolynomial n k).eval x := by
  rw [binomialCDFPolynomial,eval_finset_sum]
  apply sum_nonneg
  intro j _
  rw [bernstein_real_eval]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

theorem binomial_cdf_zero (n k : ℕ) : (binomialCDFPolynomial n k).eval 0=1 := by
  simp only [binomialCDFPolynomial,eval_finset_sum,bernsteinPolynomial.eval_at_0]
  simp

variable {V : Type} [Fintype V] [DecidableEq V]

theorem bernoulli_card_cdf_polynomial (D : Finset V) (p : unitInterval) {k : ℕ}
    (hk : k≤D.card) :
    (subsetBernoulli D p).prob (fun S => S.card≤k)=(binomialCDFPolynomial D.card k).eval (p:ℝ) := by
  rw [bernoulli_card_cdf]
  have hfilter : (range (D.card+1)).filter (fun j => j≤k)=range (k+1) := by
    ext j
    simp only [mem_filter,mem_range]
    omega
  calc
    _ = ∑ j∈range (D.card+1), if j≤k then binomialSizeMass D.card p j else 0 := by
      apply sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ = ∑ j∈range (k+1), binomialSizeMass D.card p j := by rw [← sum_filter,hfilter]
    _ = _ := by
      rw [binomialCDFPolynomial,eval_finset_sum]
      apply sum_congr rfl
      intro j _
      exact (bernstein_real_eval D.card j p).symm

end
end Cycle12
