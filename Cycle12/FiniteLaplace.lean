import Cycle12.Foundations.FiniteLaw

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
variable {Ω : Type} [Fintype Ω]

theorem finite_expect_exp_jensen (mu : FiniteLaw Ω) (f : Ω → ℝ) :
    exp (mu.expect f) ≤ mu.expect (fun x => exp (f x)) := by
  exact convexOn_exp.map_sum_le (fun x _ => mu.nonneg x) mu.total
    (fun x _ => Set.mem_univ (f x))

def finiteLaplace (mu : FiniteLaw Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  mu.expect (fun x => exp (-s*X x))

@[simp] theorem finite_laplace_zero (mu : FiniteLaw Ω) (X : Ω → ℝ) : finiteLaplace mu X 0=1 := by
  simp [finiteLaplace]

theorem finite_laplace_nonneg (mu : FiniteLaw Ω) (X : Ω → ℝ) (s : ℝ) :
    0 ≤ finiteLaplace mu X s := mu.expect_nonneg (fun _ => (exp_pos _).le)

theorem finite_laplace_derivative (mu : FiniteLaw Ω) (X : Ω → ℝ) (s : ℝ) :
    HasDerivAt (finiteLaplace mu X)
      (-mu.expect (fun x => X x*exp (-s*X x))) s := by
  have hh (x : Ω) : HasDerivAt (fun t : ℝ => mu.mass x*exp (-t*X x))
      (-mu.mass x*X x*exp (-s*X x)) s := by
    convert (((hasDerivAt_id s).neg.mul_const (X x)).exp.const_mul (mu.mass x)) using 1 <;>
      simp only [Pi.neg_apply,id_eq,neg_mul,mul_neg,one_mul,mul_assoc] <;> ring
  have hd := HasDerivAt.fun_sum (u:=univ) (fun x _ => hh x)
  convert hd using 1
  · rfl
  · simp only [FiniteLaw.expect,mul_assoc,neg_mul,sum_neg_distrib]

end
end Cycle12
