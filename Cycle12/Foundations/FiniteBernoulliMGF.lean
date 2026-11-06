import Cycle12.Foundations.FiniteBernoulli

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bernoulliSubset_expect_product (p : unitInterval) (f : V → ℝ) :
    (bernoulliSubset p).expect (fun S => ∏ v∈S, f v)=
      ∏ v, (1-(p:ℝ)+(p:ℝ)*f v) := by
  rw [show (∏ v, (1-(p:ℝ)+(p:ℝ)*f v))=∏ v, ((p:ℝ)*f v+(1-(p:ℝ))) from by
    apply prod_congr rfl; intro v _; ring]
  rw [Fintype.prod_add]
  unfold FiniteLaw.expect bernoulliSubset
  apply sum_congr rfl
  intro S _
  simp only [prod_mul_distrib,prod_const,nsmul_eq_mul,card_compl,card_univ]
  ring

theorem bernoulliSubset_count_mgf (p : unitInterval) (A : Finset V) (θ : ℝ) :
    (bernoulliSubset p).expect (fun S => exp (θ*(S∩A).card))=
      (1-(p:ℝ)+(p:ℝ)*exp θ)^A.card := by
  have hprod : ∀ S : Finset V, (∏ v∈S, if v∈A then exp θ else 1)=exp (θ*(S∩A).card) := by
    intro S
    rw [prod_ite]
    simp only [prod_const,one_pow,mul_one,filter_mem_eq_inter]
    rw [← Real.exp_nat_mul,mul_comm]
  have hh := bernoulliSubset_expect_product p (fun v => if v∈A then exp θ else 1)
  simp_rw [hprod] at hh
  rw [hh]
  have he : ∀ v : V, 1-(p:ℝ)+(p:ℝ)*(if v∈A then exp θ else 1)=
      if v∈A then 1-(p:ℝ)+(p:ℝ)*exp θ else 1 := by
    intro v; by_cases hv : v∈A <;> simp [hv]
  simp_rw [he]
  rw [prod_ite]
  simp only [filter_mem_eq_inter,univ_inter,prod_const,one_pow,mul_one]

theorem bernoulliSubset_count_mgf_le (p : unitInterval) (A : Finset V) (θ : ℝ) :
    (bernoulliSubset p).expect (fun S => exp (θ*(S∩A).card)) ≤
      exp ((p:ℝ)*(exp θ-1)*A.card) := by
  rw [bernoulliSubset_count_mgf]
  have hn : 0 ≤ 1-(p:ℝ)+(p:ℝ)*exp θ := by
    have hp := p.2.2; have hnon := mul_nonneg p.2.1 (exp_pos θ).le; linarith
  have he : 1-(p:ℝ)+(p:ℝ)*exp θ ≤ exp ((p:ℝ)*(exp θ-1)) := by
    have hh := Real.add_one_le_exp ((p:ℝ)*(exp θ-1)); linarith
  have hh := pow_le_pow_left₀ hn he A.card
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_comm (A.card:ℝ)] using hh

end
end Cycle13
