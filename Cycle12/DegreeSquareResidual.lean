import Cycle12.FiniteLaplace

namespace Cycle12
open Finset
noncomputable section
variable {V : Type} [Fintype V]

/-- Exact residual-square identity for a symmetric zero-one matrix. -/
theorem symmetric_matrix_residual_identity (A : V → V → ℝ) (d : V → ℝ)
    (hsym : ∀ i j, A i j=A j i) (hrow : ∀ i, ∑ j, A i j=d i)
    (hsq : ∀ i j, (A i j)^2=A i j) (r c : ℝ) :
    (∑ i, ∑ j, (r*A i j-d i-d j+c)^2)=
      r^2*(∑ i, d i)+2*(Fintype.card V:ℝ)*(∑ i, (d i)^2)+
      (Fintype.card V:ℝ)^2*c^2-4*r*(∑ i, (d i)^2)+
      2*r*c*(∑ i, d i)+2*(∑ i, d i)^2-4*(Fintype.card V:ℝ)*c*(∑ i, d i) := by
  have hcol (j : V) : ∑ i, A i j=d j := by
    simp_rw [hsym _ j]
    exact hrow j
  have htotal : (∑ i, ∑ j, A i j)=∑ i, d i := sum_congr rfl (fun i _ => hrow i)
  have hleft : (∑ i, ∑ j, A i j*d i)=∑ i, (d i)^2 := by
    apply sum_congr rfl
    intro i _
    rw [← sum_mul,hrow,pow_two]
  have hright : (∑ i, ∑ j, A i j*d j)=∑ j, (d j)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [← sum_mul,hcol,pow_two]
  have hexpand (i j : V) : (r*A i j-d i-d j+c)^2=
      r^2*A i j+(d i)^2+(d j)^2+c^2-
        2*r*(A i j*d i)-2*r*(A i j*d j)+2*r*c*A i j+
        2*(d i*d j)-2*c*d i-2*c*d j := by
    have hh := hsq i j
    nlinarith only [congrArg (fun z : ℝ => r^2*z) hh]
  simp only [hexpand,sum_add_distrib,sum_sub_distrib]
  simp only [← mul_sum,← sum_mul,htotal,hleft,hright,hrow,← pow_two,sum_const,card_univ,nsmul_eq_mul]
  ring

end
end Cycle12
