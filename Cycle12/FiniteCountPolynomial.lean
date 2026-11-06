import Cycle12.BernoulliListSplitting
import Cycle12.Foundations.FiniteSupport

namespace Cycle12
open Polynomial Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type} [Fintype Ω]

/-- The actual generating polynomial of a finite nonnegative integer-valued
random variable. This uses every atom of the given law. -/
def finiteCountPGF (μ : FiniteLaw Ω) (Z : Ω → ℕ) : Polynomial ℝ :=
  ∑ ω, C (μ.mass ω)*X^(Z ω)

theorem finite_count_coeff (μ : FiniteLaw Ω) (Z : Ω → ℕ) (j : ℕ) :
    (finiteCountPGF μ Z).coeff j=μ.prob (fun ω => Z ω=j) := by
  simp only [finiteCountPGF,finsetSum_coeff,coeff_C_mul_X_pow,FiniteLaw.prob,FiniteLaw.expect]
  apply sum_congr rfl
  intro ω _
  by_cases h : Z ω=j
  · simp [h]
  · simp [h,Ne.symm h]

theorem finite_count_eval_one (μ : FiniteLaw Ω) (Z : Ω → ℕ) :
    (finiteCountPGF μ Z).eval 1=1 := by
  simpa [finiteCountPGF,eval_finsetSum] using μ.total

theorem finite_count_derivative_mean (μ : FiniteLaw Ω) (Z : Ω → ℕ) :
    (finiteCountPGF μ Z).derivative.eval 1=μ.expect (fun ω => (Z ω:ℝ)) := by
  simp only [finiteCountPGF,derivative_sum,derivative_C_mul_X_pow,eval_finsetSum,
    eval_mul,eval_C,eval_pow,eval_X,one_pow,mul_one,FiniteLaw.expect]

theorem finite_count_small_tail (μ : FiniteLaw Ω) (Z : Ω → ℕ) :
    smallTailTwo (finiteCountPGF μ Z)=μ.prob (fun ω => Z ω<3) := by
  simp only [smallTailTwo,finite_count_coeff,FiniteLaw.prob,← FiniteLaw.expect_add]
  congr 1
  funext ω
  split_ifs <;> norm_num <;> omega

@[simp] theorem bernoulli_eval_one (p : ℝ) : (realBernoulliPolynomial p).eval 1=1 := by
  simp [realBernoulliPolynomial]

@[simp] theorem bernoulli_derivative_mean (p : ℝ) :
    (realBernoulliPolynomial p).derivative.eval 1=p := by
  simp [realBernoulliPolynomial,derivative_add,derivative_C_mul_X]

@[simp] theorem bernoulli_list_eval_one (l : List ℝ) : (bernoulliListPGF l).eval 1=1 := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

theorem bernoulli_list_derivative_mean (l : List ℝ) :
    (bernoulliListPGF l).derivative.eval 1=l.sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [derivative_mul,ih]

end
end Cycle12
