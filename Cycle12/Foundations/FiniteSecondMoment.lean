import Cycle12.Foundations.FiniteCantelli

namespace Cycle13.FiniteLaw
open Finset
noncomputable section
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem centered_second_moment (μ : FiniteLaw Ω) (X : Ω → ℝ) {m : ℝ}
    (hmean : μ.expect X=m) :
    μ.expect (fun ω => (X ω-m)^2)=μ.expect (fun ω => (X ω)^2)-m^2 := by
  have he : (fun ω => (X ω-m)^2)=
      (fun ω => (X ω)^2+(-2*m)*X ω+m^2) := by funext ω; ring
  rw [he,expect_add,expect_add,expect_const_mul,hmean,expect_const]
  ring

theorem expect_sum_sq (μ : FiniteLaw Ω) (X : I → Ω → ℝ) :
    μ.expect (fun ω => (∑ i, X i ω)^2)=∑ i, ∑ j, μ.expect (fun ω => X i ω*X j ω) := by
  have he : (fun ω => (∑ i, X i ω)^2)=(fun ω => ∑ i, ∑ j, X i ω*X j ω) := by
    funext ω; rw [pow_two,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum]
  rw [he,expect_sum]
  apply sum_congr rfl
  intro i _
  exact expect_sum _ _

theorem variance_sum (μ : FiniteLaw Ω) (X : I → Ω → ℝ) (m : I → ℝ)
    (hmean : ∀ i, μ.expect (X i)=m i) :
    μ.expect (fun ω => ((∑ i, X i ω)-∑ i, m i)^2)=
      ∑ i, ∑ j, (μ.expect (fun ω => X i ω*X j ω)-m i*m j) := by
  have hm : μ.expect (fun ω => ∑ i, X i ω)=∑ i, m i := by
    rw [expect_sum]; simp_rw [hmean]
  rw [centered_second_moment _ _ hm,expect_sum_sq]
  simp_rw [sum_sub_distrib]
  congr 1
  rw [pow_two,sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]

end
end Cycle13.FiniteLaw
