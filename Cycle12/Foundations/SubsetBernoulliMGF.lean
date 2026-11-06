import Cycle12.Foundations.MarkedSamplingCoupling
import Cycle12.Foundations.FiniteBernoulliMGF

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_expect_product (W : Finset V) (p : unitInterval) (f : V → ℝ) :
    (subsetBernoulli W p).expect (fun S => ∏ v∈S, f v)=
      ∏ v∈W, (1-(p:ℝ)+(p:ℝ)*f v) := by
  rw [show (∏ v∈W, (1-(p:ℝ)+(p:ℝ)*f v))=∏ v∈W, ((p:ℝ)*f v+(1-(p:ℝ))) from by
    apply prod_congr rfl; intro v _; ring]
  rw [subsetBernoulli_expect,Finset.prod_add]
  apply sum_congr rfl
  intro S hS
  have hs := mem_powerset.mp hS
  rw [subsetBernoulli_mass _ _ _ hs]
  simp only [prod_mul_distrib,prod_const,card_sdiff_of_subset hs]
  ring

theorem subsetBernoulli_count_mgf (W : Finset V) (p : unitInterval) (D : Finset V) (θ : ℝ)
    (hD : D⊆W) :
    (subsetBernoulli W p).expect (fun S => exp (θ*(S∩D).card))=
      (1-(p:ℝ)+(p:ℝ)*exp θ)^D.card := by
  have hprod : ∀ S : Finset V, (∏ v∈S, if v∈D then exp θ else 1)=exp (θ*(S∩D).card) := by
    intro S
    rw [prod_ite]
    simp only [prod_const,one_pow,mul_one,filter_mem_eq_inter]
    rw [← Real.exp_nat_mul,mul_comm]
  have hh := subsetBernoulli_expect_product W p (fun v => if v∈D then exp θ else 1)
  simp_rw [hprod] at hh
  rw [hh]
  have he : ∀ v : V, 1-(p:ℝ)+(p:ℝ)*(if v∈D then exp θ else 1)=
      if v∈D then 1-(p:ℝ)+(p:ℝ)*exp θ else 1 := by
    intro v; by_cases hv : v∈D <;> simp [hv]
  simp_rw [he]
  rw [prod_ite]
  simp only [filter_mem_eq_inter,inter_eq_right.mpr hD,prod_const,one_pow,mul_one]

theorem subsetBernoulli_count_mgf_le (W : Finset V) (p : unitInterval) (D : Finset V) (θ : ℝ)
    (hD : D⊆W) :
    (subsetBernoulli W p).expect (fun S => exp (θ*(S∩D).card)) ≤
      exp ((p:ℝ)*(exp θ-1)*D.card) := by
  rw [subsetBernoulli_count_mgf W p D θ hD]
  have hn : 0 ≤ 1-(p:ℝ)+(p:ℝ)*exp θ := by
    have hp := p.2.2; have hnon := mul_nonneg p.2.1 (exp_pos θ).le; linarith
  have he : 1-(p:ℝ)+(p:ℝ)*exp θ ≤ exp ((p:ℝ)*(exp θ-1)) := by
    have hh := Real.add_one_le_exp ((p:ℝ)*(exp θ-1)); linarith
  have hh := pow_le_pow_left₀ hn he D.card
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_comm (D.card:ℝ)] using hh

end
end Cycle13
