import Cycle12.FiniteLaplace

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
variable {I : Type} [Fintype I]

theorem finite_weighted_exp_jensen (w y : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : 0 < ∑ i, w i) :
    (∑ i, w i)*exp ((∑ i, w i*y i)/(∑ i, w i)) ≤ ∑ i, w i*exp (y i) := by
  have hj := convexOn_exp.map_centerMass_le (t:=univ) (w:=w) (p:=y)
    (fun i _ => hw i) hm (fun i _ => Set.mem_univ (y i))
  simp only [centerMass,smul_eq_mul] at hj
  have hh := mul_le_mul_of_nonneg_left hj hm.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hm.ne',one_mul,div_eq_mul_inv,mul_comm,
    Function.comp_apply] using hh

end
end Cycle12
